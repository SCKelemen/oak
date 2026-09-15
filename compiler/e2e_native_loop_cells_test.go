package compiler

// A package cell stored inside a data-dependent loop body (`count = count +
// u32(1)` beside the loop's counter) is a loop-carried variable on the
// machine side — a fresh symbol at the cell's width, paired with the Oak
// side's cell local like a register (docs/spec/94-assembler.md §9) — so
// the loop is proven with the cell's final value, where before the body
// was refused for "a store in a loop body".

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeLoopCellProgram = `Table: type = struct {
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

func TestE2ENativeLoopCarriedCellProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("loop_cell.oak", nativeLoopCellProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "loop_cell", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit tally: proven equal to its Oak body at the bit level — data-dependent loop coupled inductively (count↔global:count") || !strings.Contains(joined, "and the package state it writes (count)") {
		t.Errorf("tally's in-loop cell must be coupled and its final value decided; diagnostics:\n%s", joined)
	}
	for _, fn := range []string{"alloc", "reset"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch:\n%s", joined)
	}
}
