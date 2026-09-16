package compiler

// The OS pilot's page-table shapes that stayed trusted or were falsely
// refuted (docs/spec/94-assembler.md §9): a loop storing through a span of
// records (`s[dom].pages[j] = 0`) — its stores collected per leaf memory on
// both sides, the loop carrying no local for the span; a package cell
// assigned inside the arm of a value-position conditional (`ok ? { st =
// u8(1); idx } | { u16(0) }`) — merged on the condition, where it used to
// escape its arm and make alloc a false mismatch; a callee's cell reached
// through a caller that never names it (walk → alloc → st) — the unit's
// Globals span its callees'; and a data-dependent loop under a conditional
// — its marker guarded by the arm's condition on the Oak side as the asm
// join guards it.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeRecordLoopStoreProgram = `Table: type = struct {
  pages: [8]u64
  free_count: u16
  high_water: u16
  entry_count: [4]u16
}

st: u8

clear_pages: (s: [*]Table, dom: u32): u32 {
  j: u32 = u32(0)
  dom < len(s) ? {
    while j < u32(8) {
      s[dom].pages[j] = u64(0)
      j = j + u32(1)
    }
    j
  } | { u32(0) }
}

alloc: (s: [*]Table, dom: u32): u16 {
  idx: u16 = u16(0)
  dom < len(s) ? {
    none: Bool = s[dom].free_count == u16(0)
    none ? { st = u8(1) } | { st = st }
    ok: Bool = st == u8(0)
    ok ? {
      s[dom].free_count = s[dom].free_count - u16(1)
      idx = s[dom].free_count
      j: u32 = u32(0)
      while j < u32(4) {
        s[dom].entry_count[j] = u16(0)
        j = j + u32(1)
      }
      iu: u16 = u16(8) - s[dom].free_count
      hw: Bool = iu > s[dom].high_water
      hw ? { s[dom].high_water = iu } | { s[dom].high_water = s[dom].high_water }
    } | { idx = idx }
    idx
  } | { u16(0) }
}

walk: (s: [*]Table, dom: u32): u16 {
  n: u32 = clear_pages(s, dom)
  a: u16 = alloc(s, dom)
  a + u16_trunc_u32(n)
}

main: (): i32 {
  t: [1]Table = [Table { pages: [1, 2, 3, 4, 5, 6, 7, 8], free_count: 3, high_water: 0, entry_count: [9, 9, 9, 9] }]
  r: u16 = walk(span(&t), u32(0))
  (r == u16(10) && t[0].pages[7] == u64(0) && t[0].high_water == u16(6) && t[0].entry_count[3] == u16(0) && st == u8(0)) ? 42 | 1
}
`

const nativeGuardedLoopStoreProgram = `Table: type = struct {
  pages: [8]u64
  free_count: u16
  entry_count: [4]u16
}

clear_pages: (s: [*]Table, dom: u32, n: u32): u32 {
  j: u32 = u32(0)
  dom < len(s) && n <= u32(8) ? {
    while j < n {
      s[dom].pages[j] = u64(0)
      j = j + u32(1)
    }
    j
  } | { u32(0) }
}

main: (): i32 {
  t: [1]Table = [Table { pages: [1, 2, 3, 4, 5, 6, 7, 8], free_count: 3, entry_count: [9, 9, 9, 9] }]
  n: u32 = clear_pages(span(&t), u32(0), u32(6))
  (n == u32(6) && t[0].pages[5] == u64(0) && t[0].pages[6] == u64(7)) ? 42 | 1
}
`

func nativeVerdicts(t *testing.T, name, src string) (int, bool, string) {
	t.Helper()
	var infos []string
	comp := New().WithSource(name+".oak", src).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, name, comp)
	return code, abnormal, strings.Join(infos, "\n")
}

func TestE2ENativeRecordLoopStoresProven(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeVerdicts(t, "record_loop_store", nativeRecordLoopStoreProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, want := range []string{
		"asm unit clear_pages: proven equal to its Oak body at the bit level",
		"asm unit alloc: proven equal to its Oak body at the bit level",
		"the package state it writes (st) and the span memory it writes (s.entry_count, s.free_count, s.high_water)",
		"asm unit walk: proven equal to its Oak body at the bit level",
		"(callees taken at their Oak bodies: clear_pages, alloc) and the package state it writes (st) and the span memory it writes (s.entry_count, s.free_count, s.high_water, s.pages)",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("diagnostics lack %q:\n%s", want, joined)
		}
	}
	if strings.Contains(joined, "disagrees") || strings.Contains(joined, "mismatch") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "record_loop_store_c", New().WithSource("record_loop_store.oak", nativeRecordLoopStoreProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestE2ENativeGuardedRecordLoopProven(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeVerdicts(t, "guarded_loop_store", nativeGuardedLoopStoreProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// Only the leaf the loop stores to: the loop marks one memory per leaf
	// of the record span and drops the marks nothing wrote, so the leaves
	// this body leaves alone are not among the memories it is proven in
	// (asm/loops.go, the marker under the loop's entry test).
	if !strings.Contains(joined, "asm unit clear_pages: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively") || !strings.Contains(joined, "span memory it writes (s.pages)") {
		t.Errorf("the guarded data-dependent loop must be proven with the leaf memory it writes:\n%s", joined)
	}
	if strings.Contains(joined, "span memory it writes (s.entry_count") {
		t.Errorf("clear_pages writes no counter and must not be proven in their memories:\n%s", joined)
	}
	// The final verdict, not a candidate transform's ("keeps its …
	// (the … form was judged …)"), decides.
	for _, line := range strings.Split(joined, "\n") {
		if strings.HasPrefix(line, "asm unit clear_pages:") && strings.Contains(line, "evidence, not proof") {
			t.Errorf("the memories after the loop were not proven equal:\n%s", joined)
		}
	}
}

// Package cells around a data-dependent loop are compared after the loops
// under the coupling (`st = u8(0)` after reset's zeroing loop, then a call
// that writes it); a cell stored inside the loop body stays trusted, never
// a mismatch.
const nativeCellsAroundLoopProgram = `Table: type = struct {
  pages: [8]u64
  free_count: u16
}

st: u8
count: u32

alloc: (s: [*]Table, dom: u32): u16 {
  idx: u16 = u16(0)
  dom < len(s) ? {
    none: Bool = s[dom].free_count == u16(0)
    none ? { st = u8(1) } | { st = st }
    ok: Bool = st == u8(0)
    ok ? {
      s[dom].free_count = s[dom].free_count - u16(1)
      idx = s[dom].free_count
    } | { idx = idx }
    idx
  } | { u16(0) }
}

reset: (s: [*]Table, dom: u32, n: u32): u16 {
  dom < len(s) && n <= u32(8) ? {
    j: u32 = u32(0)
    while j < n {
      s[dom].pages[j] = u64(0)
      j = j + u32(1)
    }
    s[dom].free_count = u16(3)
    st = u8(0)
    alloc(s, dom)
  } | { u16(0) }
}

tally: (s: []Table, dom: u32, n: u32): u32 {
  acc: u32 = u32(0)
  dom < len(s) && n <= u32(8) ? {
    j: u32 = u32(0)
    while j < n {
      acc = acc + u32_trunc_u64(s[dom].pages[j])
      count = count + u32(1)
      j = j + u32(1)
    }
    acc
  } | { u32(0) }
}

main: (): i32 {
  t: [1]Table = [Table { pages: [1, 2, 3, 4, 5, 6, 7, 8], free_count: 0 }]
  r: u16 = reset(span(&t), u32(0), u32(6))
  k: u32 = tally(view(&t), u32(0), u32(8))
  (r == u16(2) && k == u32(15) && count == u32(8) && st == u8(0)) ? 42 | 1
}
`

func TestE2ENativeCellsAroundLoopProven(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeVerdicts(t, "cells_around_loop", nativeCellsAroundLoopProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit reset: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively") || !strings.Contains(joined, "and the span memory it writes (s.free_count, s.pages) and the package state it writes (st)") {
		t.Errorf("reset must be proven with its cell and leaf memories:\n%s", joined)
	}
	// A cell stored in the loop body is loop-carried on the machine side
	// (compiler/e2e_native_loop_cells_test.go): tally is proven too.
	if !strings.Contains(joined, "asm unit tally: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively (count↔global:count") {
		t.Errorf("tally (a cell stored in the loop body) must be proven with its cell coupled:\n%s", joined)
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "cells_around_loop_c", New().WithSource("cells_around_loop.oak", nativeCellsAroundLoopProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The OS pilot's alloc_table shape at its inducted size: a store before an
// inducted loop inside the arm `ok ? { s[dom].free_count = …; while j <
// entries { … } }`. The machine reached the loop under `ok` and its store
// is unguarded there; the Oak side's store carries `ok` as its guard, so
// the induction's base — the memories at the loop's entry — is compared
// under the machine's reaching condition. reset's three loops are
// inducted (2048 entries here scaled to 128, still past the unroll bound).
const nativeStage2AllocProgram = `max_pages: u16 = u16(2)
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

main: (): i32 {
  r: [1]Regime
  reset(span(&r), u32(0), u64(65536))
  (r[0].root == u16(0) && r[0].free_count == u16(1) && r[0].high_water == u16(1) && r[0].pages[3] == u64(0) && st == u8(0)) ? 42 | 1
}
`

func TestE2ENativeStage2AllocTableProven(t *testing.T) {
	requireArm64Host(t)
	code, abnormal, joined := nativeVerdicts(t, "stage2_alloc", nativeStage2AllocProgram)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// Every leaf memory the loop marks is compared after it, written or not.
	if !strings.Contains(joined, "asm unit alloc_table: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively") || !strings.Contains(joined, "and the span memory it writes (s.entry_count, s.free_count, s.free_stack, s.high_water, s.pages, s.pool_base, s.root) and the package state it writes (st)") {
		t.Errorf("alloc_table must be proven with its cell and leaf memories:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit reset: proven equal to its Oak body at the bit level — 3 data-dependent loops coupled inductively") {
		t.Errorf("reset's inducted loops must be proven:\n%s", joined)
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
}
