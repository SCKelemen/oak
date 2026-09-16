package compiler

// A callee with an inducted loop called inside a caller's arm — the OS
// pilot's walk_leaf calling alloc_table under `invalid && create == 1` —
// is proven through the call summary: the callee's loop events carry the
// condition under which they are reached (the machine's path at the call
// and the callee's own arm), so the induction's base and body premises
// assume it (docs/spec/94-assembler.md §9). Before, the caller was
// evidence: "the memory of s.free_count at loop 1's entry was not proven
// equal" (the callee's store before its loop is guarded by the callee's
// `ok` on the Oak side and unguarded on the machine's path).

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeCalleeLoopReachedProgram = `max_pages: u16 = u16(2)
entries: u32 = u32(128)

Regime: type = struct {
  pages: [256]u64
  free_stack: [2]u16
  free_count: u16
  high_water: u16
  entry_count: [2]u16
  root: u16
  pool_base: u64
}

st: u8

cell: (table: u16, idx: u32): u32 { u32(table) * entries + idx }

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
  st = u8(0)
  s[dom].root = alloc_table(s, dom)
}

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

walk: (s: [*]Regime, dom: u32, create: u8): u16 {
  d0: u64 = s[dom].pool_base
  invalid: Bool = (d0 & u64(1)) == u64(0)
  invalid && create == u8(1) ? { alloc_table(s, dom) } | { u16(7) }
}

main: (): i32 {
  r: [1]Regime
  reset(span(&r), u32(0), u64(65536))
  w: u16 = walk(span(&r), u32(0), u8(1))
  (w == u16(1) && st == u8(0)) ? 42 | 1
}
`

func TestE2ENativeCalleeLoopReachedProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("callee_loop.oak", nativeCalleeLoopReachedProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "callee_loop", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit walk: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively") || !strings.Contains(joined, "asm unit alloc_table: proven") {
		t.Errorf("walk must be proven through alloc_table's summarized loop; diagnostics:\n%s", joined)
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
}
