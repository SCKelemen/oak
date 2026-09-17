package compiler

// The OS pilot's addr_space.map_page at a smaller geometry: a two-level
// page walk over a record span whose leaf descriptor depends on a
// permission, with the table allocation's zeroing loop inlined. The span
// memory after the loops is proven by cases (docs/spec/94-assembler.md
// §9, asm/span_cases.go): the machine writes a constant descriptor per
// permission branch where the Oak side writes one value with the
// permission's conditionals inside it, and the two spell the leaf index
// under different masks. The table holds 128 entries, past the unrolling
// bound, so the zeroing loop is proven as a loop, as the pilot's is.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeMapPageProgram = `max_pages: u16 = u16(4)
entries: u32 = u32(128)
page_size: u64 = u64(16384)
l0_shift: u64 = u64(21)
l0_mask: u64 = u64(127)
l1_shift: u64 = u64(14)
l1_mask: u64 = u64(127)
va_limit: u64 = u64(0x100000000)
desc_valid: u64 = u64(1)
desc_page: u64 = u64(2)
desc_pa_mask: u64 = u64(0x0000FFFFFFFFF000)
ap_shift: u64 = u64(6)

Regime: type = struct {
  pages: [512]u64
  free_stack: [4]u16
  free_count: u16
  high_water: u16
  entry_count: [4]u16
  root: u16
  mapped_pages: u32
  pool_base: u64
}

st: u8

cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }
desc_af: (): u64 { u64(1) << u64(10) }
desc_sh: (): u64 { u64(3) << u64(8) }
desc_ng: (): u64 { u64(1) << u64(11) }
desc_pxn: (): u64 { u64(1) << u64(53) }
desc_uxn: (): u64 { u64(1) << u64(54) }
ap_of: (perm: u8): u64 {
  a: u64 = u64(3)
  rw: Bool = perm == u8(1)
  rw ? { a = u64(1) }
  a
}
xn_of: (perm: u8): u64 {
  x: u64 = desc_uxn() | desc_pxn()
  rx: Bool = perm == u8(2)
  rx ? { x = desc_pxn() }
  x
}
page_desc: (pa: u64, perm: u8): u64 {
  pa | desc_af() | desc_sh() | desc_ng() | (ap_of(perm) << ap_shift) | xn_of(perm) | desc_page | desc_valid
}
table_desc: (pa: u64): u64 { pa | desc_page | desc_valid }
page_pa: (pool_base: u64, index: u16): u64 { pool_base + u64(index) * page_size }
pa_index: (pool_base: u64, pa: u64): u16 { u16_trunc_u64((pa - pool_base) / page_size) }

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

check_range: (va: u64, pa: u64): () {
  un: Bool = st == u8(0) && (va % page_size != u64(0) || pa % page_size != u64(0))
  st = un ? u8(4) | st
  oor1: Bool = st == u8(0) && va >= va_limit
  st = oor1 ? u8(5) | st
  oor2: Bool = st == u8(0) && (pa & ^desc_pa_mask) != u64(0)
  st = oor2 ? u8(5) | st
}

map_page: (s: [*]Regime, dom: u32, va: u64, pa: u64, perm: u8): u8 {
  st = u8(0)
  check_range(va, pa)
  go: Bool = st == u8(0)
  go ? {
    table: u16 = s[dom].root
    idx0: u64 = (va >> l0_shift) & l0_mask
    d0: u64 = s[dom].pages[cell(table, u32_trunc_u64(idx0))]
    invalid: Bool = (d0 & desc_valid) == u64(0)
    invalid ? {
      ai: u16 = alloc_table(s, dom)
      setd: Bool = st == u8(0)
      setd ? {
        s[dom].pages[cell(table, u32_trunc_u64(idx0))] = table_desc(page_pa(s[dom].pool_base, ai))
        s[dom].entry_count[u32(table)] = s[dom].entry_count[u32(table)] + u16(1)
      } | {
      }
    } | {
    }
    ok: Bool = st == u8(0)
    ok ? {
      leaf: u16 = pa_index(s[dom].pool_base, s[dom].pages[cell(table, u32_trunc_u64(idx0))] & desc_pa_mask)
      idx1: u64 = (va >> l1_shift) & l1_mask
      d: u64 = s[dom].pages[cell(leaf, u32_trunc_u64(idx1))]
      already: Bool = (d & desc_valid) != u64(0)
      st = already ? u8(2) | st
      wok: Bool = st == u8(0)
      wok ? {
        s[dom].pages[cell(leaf, u32_trunc_u64(idx1))] = page_desc(pa, perm)
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

main: (): i32 {
  regimes: [1]Regime
  s: [*]Regime = span(&regimes)
  s[0].free_count = u16(3)
  s[0].free_stack[2] = u16(1)
  s[0].free_stack[1] = u16(2)
  s[0].free_stack[0] = u16(3)
  first: u8 = map_page(s, u32(0), u64(3) * page_size, u64(8) * page_size, u8(1))
  second: u8 = map_page(s, u32(0), u64(3) * page_size, u64(9) * page_size, u8(2))
  (first == u8(0) && second == u8(2) && s[0].mapped_pages == u32(1)) ? 42 | 1
}
`

func TestE2ENativeMapPageProvenByCases(t *testing.T) {
	requireArm64Host(t)
	skipInShort(t)
	var infos []string
	comp := New().WithSource("map_page.oak", nativeMapPageProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "map_page", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, unit := range []string{"map_page", "alloc_table"} {
		if !strings.Contains(joined, "asm unit "+unit+": proven") {
			t.Fatalf("%s must be proven:\n%s", unit, joined)
		}
	}
}
