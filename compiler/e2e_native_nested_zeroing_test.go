package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The OS pilot's reset at the scale that unrolls: two nested counted
// loops over module constants (four pages of sixty-four entries), a
// guarded store each iteration — 256 trap guards on one path. A guard
// forks nothing; counted as a path each, they exhausted the path budget
// ("more paths than the verifier's budget" at 3ba8b5ae, where the pilot's
// pin had reset proven). Guards draw on their own budget now
// (asm.guardBudget, docs/spec/94-assembler.md §9).
const nativeNestedZeroingProgram = `max_pages: u16 = u16(4)
entries: u32 = u32(64)

Regime: type = struct {
  pages: [256]u64
  free_stack: [4]u16
  free_count: u16
  high_water: u16
  entry_count: [4]u16
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

// Keep both the caller's path to alloc_table and alloc_table's internal
// ok path when its inducted loop becomes walk's call-summary event.
walk: (s: [*]Regime, dom: u32, create: u8): u64 {
  create == u8(1) ? {
    index: u16 = alloc_table(s, dom)
    st == u8(0) ? { s[dom].pages[cell(index, u32(0))] } | { u64(0) }
  } | { u64(0) }
}

main: (): i32 {
  r: [1]Regime
  reset(span(&r), u32(0), u64(65536))
  (r[0].root == u16(0) && r[0].free_count == u16(3) && r[0].high_water == u16(1) && r[0].pages[3] == u64(0) && st == u8(0)) ? 42 | 1
}
`

func TestE2ENativeNestedZeroingLoopProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("zeroing.oak", nativeNestedZeroingProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_nested_zeroing", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("nested zeroing: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if strings.Contains(joined, "asm unit reset: not verified") {
		t.Errorf("reset must not be refused by a budget:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit reset: proven equal to its Oak body") {
		t.Errorf("reset must be proven at the scale that unrolls:\n%s", joined)
	}
	if !strings.Contains(joined, "reset: 1 element guard(s) elided under the checker's own facts") {
		t.Errorf("reset's inlined cell index must carry the two loop bounds into native lowering:\n%s", joined)
	}
}
