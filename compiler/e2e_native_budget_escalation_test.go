package compiler

// The OS pilot's stage2 page-table module at a table size past the unroll
// bound: translate and unmap_page are two hundred term nodes of 64-bit
// descriptor arithmetic over three memory reads whose diagrams exceed the
// base node budget under every variable order and the case split, and
// close at eleven million nodes under the escalated budget a small term may
// claim (docs/spec/94-assembler.md §8). Before, both were evidence.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeStage2ReplicaProgram = `max_pages: u16 = u16(2)
entries: u32 = u32(128)
page_size: u64 = u64(16384)
l0_shift: u64 = u64(25)
l0_mask: u64 = u64(1)
l1_shift: u64 = u64(14)
l1_mask: u64 = u64(127)
ipa_limit: u64 = u64(0x100000000)

desc_valid: u64 = u64(1)
desc_table: u64 = u64(2)
desc_af: u64 = u64(0x400)
desc_sh_inner: u64 = u64(0x300)
desc_s2ap_rw: u64 = u64(0xC0)
desc_pa_mask: u64 = u64(0x0000FFFFFFFFF000)

Regime: type = struct {
  pages: [256]u64
  free_stack: [2]u16
  free_count: u16
  high_water: u16
  entry_count: [2]u16
  root: u16
  mapped_pages: u32
  pool_base: u64
  pad: [2]u64
}

// Per-call scratch (single-threaded, one operation at a time).
st: u8
trans_result: u64

// Flat index of entry 'idx' in table 'table' (24 tables of 'entries' each).
cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }

page_desc: (pa: u64, attrbits: u64): u64 {
  pa | desc_af | desc_sh_inner | desc_s2ap_rw | (attrbits << u64(2)) | desc_table | desc_valid
}

table_desc: (pa: u64): u64 { pa | desc_table | desc_valid }

page_pa: (pool_base: u64, index: u16): u64 { pool_base + u64(index) * page_size }
pa_index: (pool_base: u64, pa: u64): u16 { u16_trunc_u64((pa - pool_base) / page_size) }

reset: (s: [*]Regime, dom: u32, pool_base: u64): () {
  s[dom].pool_base = pool_base
  i: u16 = u16(0)
  while i < max_pages {
    j: u32 = u32(0)
    while j < entries {
      s[dom].pages[cell(i, j)] = u64(0)
      j = j + u32(1)
    }
    s[dom].free_stack[u32(i)] = max_pages - u16(1) - i
    s[dom].entry_count[u32(i)] = u16(0)
    i = i + u16(1)
  }
  s[dom].free_count = max_pages
  s[dom].high_water = u16(0)
  s[dom].mapped_pages = u32(0)
  st = u8(0)
  s[dom].root = alloc_table(s, dom)
}

// Pop a page off this regime's free list, clear it, and return its index.
// OutOfTablePages (st = 1) when empty, in which case the caller must have
// checked st before using the returned index (0 then, never used as a table).
alloc_table: (s: [*]Regime, dom: u32): u16 {
  idx: u16 = u16(0)
  none: Bool = s[dom].free_count == u16(0)
  none ? {
    st = u8(1)
  } | {
  }
  ok: Bool = st == u8(0)
  ok ? {
    s[dom].free_count = s[dom].free_count - u16(1)
    idx = s[dom].free_stack[u32(s[dom].free_count)]
    j: u32 = u32(0)
    while j < entries {
      s[dom].pages[cell(idx, j)] = u64(0)
      j = j + u32(1)
    }
    s[dom].entry_count[u32(idx)] = u16(0)
    iu: u16 = max_pages - s[dom].free_count
    hw: Bool = iu > s[dom].high_water
    hw ? {
      s[dom].high_water = iu
    } | {
    }
  } | {
  }
  idx
}

free_table: (s: [*]Regime, dom: u32, index: u16): () {
  s[dom].free_stack[u32(s[dom].free_count)] = index
  s[dom].free_count = s[dom].free_count + u16(1)
}

check_range: (ipa: u64, pa: u64): () {
  un: Bool = st == u8(0) && (ipa % page_size != u64(0) || pa % page_size != u64(0))
  st = un ? u8(4) | st
  oor1: Bool = st == u8(0) && ipa >= ipa_limit
  st = oor1 ? u8(5) | st
  oor2: Bool = st == u8(0) && (pa & ^desc_pa_mask) != u64(0)
  st = oor2 ? u8(5) | st
}

// Descend to the leaf table for ipa; allocate the intermediate on create.
// Returns the leaf table index; walk_null (a local) is set when create = 0 and
// a step is missing, in which case the returned index is the root, not a leaf,
// and the caller must have checked st/create so it is never used as a leaf.
walk_leaf: (s: [*]Regime, dom: u32, ipa: u64, create: u8): u16 {
  walk_null: u8 = u8(0)
  table: u16 = s[dom].root
  idx: u64 = (ipa >> l0_shift) & l0_mask
  d: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx))]
  invalid: Bool = (d & desc_valid) == u64(0)
  invalid ? {
    nocreate: Bool = create == u8(0)
    walk_null = nocreate ? u8(1) | walk_null
    docreate: Bool = create == u8(1)
    docreate ? {
      ai: u16 = alloc_table(s, dom)
      setd: Bool = st == u8(0)
      setd ? {
        s[dom].pages[cell(table, u32_trunc_u64(idx))] = table_desc(page_pa(s[dom].pool_base, ai))
        s[dom].entry_count[u32(table)] = s[dom].entry_count[u32(table)] + u16(1)
      } | {
      }
    } | {
    }
  } | {
  }
  cont: Bool = st == u8(0) && walk_null == u8(0)
  cont ? {
    d2: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx))]
    table = pa_index(s[dom].pool_base, d2 & desc_pa_mask)
  } | {
  }
  table
}

// Map one hardware page (== one custody granule at 16 KiB).
map_page: (s: [*]Regime, dom: u32, ipa: u64, pa: u64, attrbits: u64): u8 {
  st = u8(0)
  check_range(ipa, pa)
  go: Bool = st == u8(0)
  go ? {
    leaf: u16 = walk_leaf(s, dom, ipa, u8(1))
    ok: Bool = st == u8(0)
    ok ? {
      idx: u64 = (ipa >> l1_shift) & l1_mask
      d: u64 = s[dom].pages[cell(leaf, u32_trunc_u64(idx))]
      already: Bool = (d & desc_valid) != u64(0)
      st = already ? u8(2) | st
      wok: Bool = st == u8(0)
      wok ? {
        s[dom].pages[cell(leaf, u32_trunc_u64(idx))] = page_desc(pa, attrbits)
        s[dom].entry_count[u32(leaf)] = s[dom].entry_count[u32(leaf)] + u16(1)
        s[dom].mapped_pages = s[dom].mapped_pages + u32(1)
      } | {
      }
    } | {
    }
  } | {
  }
  st
}

// Unmap one page; reclaim the leaf table if it empties (two-level: only the
// leaf can be reclaimed, the root never is).
unmap_page: (s: [*]Regime, dom: u32, ipa: u64): u8 {
  st = u8(0)
  check_range(ipa, u64(0))
  go: Bool = st == u8(0)
  go ? {
    table: u16 = s[dom].root
    idx0: u64 = (ipa >> l0_shift) & l0_mask
    d0: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx0))]
    nm: Bool = (d0 & desc_valid) == u64(0)
    st = nm ? u8(3) | st
    cont: Bool = st == u8(0)
    cont ? {
      leaf: u16 = pa_index(s[dom].pool_base, d0 & desc_pa_mask)
      lidx: u64 = (ipa >> l1_shift) & l1_mask
      dl: u64 = s[dom].pages[cell(leaf, u32_trunc_u64(lidx))]
      nm2: Bool = (dl & desc_valid) == u64(0)
      st = nm2 ? u8(3) | st
      clr: Bool = st == u8(0)
      clr ? {
        s[dom].pages[cell(leaf, u32_trunc_u64(lidx))] = u64(0)
        s[dom].entry_count[u32(leaf)] = s[dom].entry_count[u32(leaf)] - u16(1)
        s[dom].mapped_pages = s[dom].mapped_pages - u32(1)
        empty: Bool = s[dom].entry_count[u32(leaf)] == u16(0)
        empty ? {
          s[dom].pages[cell(table, u32_trunc_u64(idx0))] = u64(0)
          s[dom].entry_count[u32(table)] = s[dom].entry_count[u32(table)] - u16(1)
          free_table(s, dom, leaf)
        } | {
        }
      } | {
      }
    } | {
    }
  } | {
  }
  st
}

// Software walk: 1 with the PA in trans_result, or 0 for no mapping.
translate: (s: [*]Regime, dom: u32, ipa: u64): u8 {
  trans_result = u64(0)
  r: u8 = u8(1)
  oor: Bool = ipa >= ipa_limit
  r = oor ? u8(0) | r
  go: Bool = r == u8(1)
  go ? {
    table: u16 = s[dom].root
    idx0: u64 = (ipa >> l0_shift) & l0_mask
    d0: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx0))]
    inv0: Bool = (d0 & desc_valid) == u64(0)
    r = inv0 ? u8(0) | r
    cont: Bool = r == u8(1)
    cont ? {
      leaf: u16 = pa_index(s[dom].pool_base, d0 & desc_pa_mask)
      idx1: u64 = (ipa >> l1_shift) & l1_mask
      d: u64 = s[dom].pages[cell(leaf, u32_trunc_u64(idx1))]
      inv1: Bool = (d & desc_valid) == u64(0)
      r = inv1 ? u8(0) | r
      fin: Bool = r == u8(1)
      trans_result = fin ? ((d & desc_pa_mask & ^(page_size - u64(1))) | (ipa & (page_size - u64(1)))) | trans_result
    } | {
    }
  } | {
  }
  r
}

// The real PA of this regime's root table — the value for VTTBR_EL2 BADDR
// (VMID and other high bits are OR'd in by the consumer).
get_root_pa: (s: [*]Regime, dom: u32): u64 { page_pa(s[dom].pool_base, s[dom].root) }

get_trans_result: (): u64 { trans_result }
get_free_count: (s: [*]Regime, dom: u32): u16 { s[dom].free_count }
get_in_use: (s: [*]Regime, dom: u32): u16 { max_pages - s[dom].free_count }
get_high_water: (s: [*]Regime, dom: u32): u16 { s[dom].high_water }
get_mapped_pages: (s: [*]Regime, dom: u32): u32 { s[dom].mapped_pages }
get_entry_count: (s: [*]Regime, dom: u32, i: u32): u16 { s[dom].entry_count[i] }

main: (): i32 {
  r: [1]Regime
  reset(span(&r), u32(0), u64(65536))
  a: u8 = map_page(span(&r), u32(0), u64(16384), u64(32768), u64(0x400))
  b: u8 = translate(span(&r), u32(0), u64(16384))
  c: u8 = unmap_page(span(&r), u32(0), u64(16384))
  (a == u8(0) && b == u8(1) && c == u8(0)) ? 42 | 1
}
`

func TestE2ENativeStage2ReplicaProvenUnderEscalatedBudget(t *testing.T) {
	requireArm64Host(t)
	skipInShort(t)
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	var infos []string
	comp := New().WithSource("stage2_replica.oak", nativeStage2ReplicaProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "stage2_replica", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"translate", "unmap_page", "map_page", "walk_leaf", "alloc_table", "reset", "check_range", "free_table"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
}
