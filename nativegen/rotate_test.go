package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// A hoisted loop's body begins with a guard's compare (docs/spec/94-assembler.md
// §9 "Bottom-tested loops"): the exit run ends at its last exit branch,
// the compare after it is the body's, and the loop rotates — the entry
// test right before the header, the tail test ending in the
// complemented back edge, no unconditional jump left.
func TestRotateLoopAfterHoistedInvariants(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x", Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	items := []asm.Item{
		asm.Label{Name: "head_1"},
		ins("mov", w(4), asm.Register{Text: "wzr"}),
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("cmp", w(2), w(1)),
		bc("hs", "trap_3"),
		ins("umaddl", x(15), w(2), w(19), x(0)),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("cmp", w(4), asm.Immediate{Value: 64}),
		bc("hs", "trap_3"),
		ins("str", x(17), x(15)),
		ins("add", w(4), w(4), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
		asm.Label{Name: "trap_3"},
		ins("brk", asm.Immediate{Value: 1}),
	}
	out, rotated := rotateLoops(items)
	if rotated != 1 {
		t.Fatalf("rotated %d loops, want 1", rotated)
	}
	var spelled []string
	for _, item := range out {
		spelled = append(spelled, strings.TrimSpace(fmt.Sprint(item)))
	}
	got := strings.Join(spelled, "\n")
	want := strings.Join([]string{
		"{head_1 0}", "mov w, wzr", "cmp w, w", "b.hs done_5", "cmp w, w", "b.hs trap_3", "umaddl x, w, w, x",
		"cmp w, w", "b.hs done_5", // the entry test
		"{loop_4 0}",
		"cmp w, #64", "b.hs trap_3", "str x, x", "add w, w, #1", // the body, the guard's compare first
		"cmp w, w", "b.lo loop_4", // the tail test
		"{done_5 0}", "ret", "{trap_3 0}", "brk #1",
	}, "\n")
	if got != want {
		t.Fatalf("rotated items:\n%s\nwant:\n%s", got, want)
	}
}

// A loop whose exit test hides a later test behind a setup instruction is
// not rotated, and neither is one another branch enters at its header.
func TestRotateLoopRefusals(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	hidden := []asm.Item{
		asm.Label{Name: "loop_4"},
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("sub", w(9), w(3), asm.Immediate{Value: 4}),
		ins("cmp", w(4), w(9)),
		bc("hi", "done_5"),
		ins("add", w(4), w(4), asm.Immediate{Value: 4}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	if _, rotated := rotateLoops(hidden); rotated != 0 {
		t.Errorf("a test behind a setup instruction rotated %d loops, want 0", rotated)
	}
	entered := []asm.Item{
		ins("cbz", w(5), asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("add", w(4), w(4), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	if _, rotated := rotateLoops(entered); rotated != 0 {
		t.Errorf("a header another branch reaches rotated %d loops, want 0", rotated)
	}
}
