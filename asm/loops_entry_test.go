package asm

import (
	"strconv"
	"testing"
)

// The entry-only tests before a loop header (docs/spec/94-assembler.md §9
// "Loop invariants"): a run of compares and branches to the exit label
// over registers the loop never writes, ending in a branch.
func TestInvariantEntryTests(t *testing.T) {
	w := func(n int) Register { return Register{Text: "w" + strconv.Itoa(n), Class: ClassW, Num: n} }
	x := func(n int) Register { return Register{Text: "x" + strconv.Itoa(n), Class: ClassX, Num: n} }
	ins := func(m string, ops ...Operand) Instruction { return Instruction{Mnemonic: m, Operands: ops} }
	bc := func(cond, target string) Instruction {
		return Instruction{Mnemonic: "b.", Cond: cond, Operands: []Operand{Symbol{Name: target}}}
	}
	items := []Item{
		ins("mov", w(3), Register{Text: "wzr", Class: ClassW, Num: 31}), // 0
		ins("sub", w(14), w(20), Immediate{Value: 4}),                   // 1
		ins("cmp", w(20), Immediate{Value: 4}),                          // 2
		bc("lo", "done_5"),                                              // 3
		Label{Name: "loop_4"},                                           // 4
		ins("cmp", w(3), w(14)),                                         // 5
		bc("hi", "done_5"),                                              // 6
		ins("ldr", x(9), Memory{Base: x(19)}),                           // 7
		ins("add", x(2), x(2), x(9)),                                    // 8
		ins("add", w(3), w(3), Immediate{Value: 4}),                     // 9
		ins("b", Symbol{Name: "loop_4"}),                                // 10
		Label{Name: "done_5"},                                           // 11
		ins("ret"),
	}
	labels := map[string]int{"loop_4": 4, "done_5": 11}
	if start := invariantEntryTests(items, labels, 4, 11, 4, 10); start != 2 {
		t.Errorf("the run `cmp w20, #4; b.lo done_5` starts at 2, got %d", start)
	}
	// The loop writes w20: no entry-only test.
	written := append([]Item(nil), items...)
	written[8] = ins("add", w(20), w(20), Immediate{Value: 1})
	if start := invariantEntryTests(written, labels, 4, 11, 4, 10); start != 4 {
		t.Errorf("a test over a register the loop writes is not entry-only, got start %d", start)
	}
	// A branch to another label ends the run; a trailing compare is the
	// header's own and leaves no run.
	other := append([]Item(nil), items...)
	other[3] = bc("lo", "elsewhere")
	if start := invariantEntryTests(other, labels, 4, 11, 4, 10); start != 4 {
		t.Errorf("a branch elsewhere is not an exit, got start %d", start)
	}
	trailing := []Item{ins("cmp", w(20), Immediate{Value: 4}), bc("lo", "done_5"), ins("cmp", w(3), w(14)), Label{Name: "loop_4"}}
	if start := invariantEntryTests(trailing, map[string]int{"done_5": 9, "loop_4": 3}, 3, 9, 3, 8); start != 3 {
		t.Errorf("a trailing compare leaves no run, got start %d", start)
	}
}
