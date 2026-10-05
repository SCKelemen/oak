package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// Five element bases of one record (docs/spec/94-assembler.md §9 "Loop
// invariants", `shared`): each is `movz #80; umaddl base; add offset`
// over invariant registers. The first chain hoists whole; the later
// constants and multiplies compute what the preheader already holds, so
// they disappear and only their offsets take a register — six registers
// for fourteen instructions, and the loop keeps its loads alone.
func TestHoistInvariantsSharesEqualValues(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	elem := func(base asm.Register, index asm.Register) asm.Memory {
		return asm.Memory{Base: base, Index: &index, Extend: "uxtw"}
	}
	chain := func(k, base, off int, offset int64, into int) []asm.Item {
		items := []asm.Item{
			ins("movz", w(k), asm.Immediate{Value: 80}),
			ins("umaddl", x(base), w(2), w(k), x(0)),
		}
		addr := x(base)
		if offset != 0 {
			items = append(items, ins("add", x(off), x(base), asm.Immediate{Value: offset}))
			addr = x(off)
		}
		return append(items, ins("ldrb", w(into), elem(addr, w(6))))
	}
	var items []asm.Item
	items = append(items,
		asm.Label{Name: "head_1"},
		ins("mov", w(6), asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(6), asm.Immediate{Value: 16}),
		bc("hs", "done_5"),
	)
	items = append(items, chain(10, 9, 10, 64, 7)...)
	items = append(items, chain(9, 11, 0, 0, 21)...)
	items = append(items, chain(11, 9, 11, 16, 22)...)
	items = append(items, chain(9, 10, 9, 32, 23)...)
	items = append(items, chain(10, 11, 10, 48, 24)...)
	items = append(items,
		ins("add", w(7), w(7), w(21)),
		ins("add", w(7), w(7), w(22)),
		ins("add", w(7), w(7), w(23)),
		ins("add", w(7), w(7), w(24)),
		ins("add", w(6), w(6), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	)
	out, taken, changed, wanted := hoistInvariants(items, registersNamed(items), map[string]map[int]bool{}, nil, nil, "trap_3")
	if changed != 1 || wanted != 0 || len(taken) != 6 {
		t.Fatalf("changed %d, wanted %d, taken %v", changed, wanted, taken)
	}
	var spelled []string
	for _, item := range out {
		spelled = append(spelled, strings.TrimSpace(fmt.Sprint(item)))
	}
	got := strings.Join(spelled, "\n")
	r := func(i int) string { return itoa(taken[i]) }
	want := strings.Join([]string{
		"{head_1 0}", "mov w6, wzr",
		"movz w" + r(0) + ", #80",
		"umaddl x" + r(1) + ", w2, w" + r(0) + ", x0",
		"add x" + r(2) + ", x" + r(1) + ", #64",
		"add x" + r(3) + ", x" + r(1) + ", #16",
		"add x" + r(4) + ", x" + r(1) + ", #32",
		"add x" + r(5) + ", x" + r(1) + ", #48",
		"{loop_4 0}", "cmp w6, #16", "b.hs done_5",
		"ldrb w7, [x" + r(2) + ", w6, uxtw]",
		"ldrb w21, [x" + r(1) + ", w6, uxtw]",
		"ldrb w22, [x" + r(3) + ", w6, uxtw]",
		"ldrb w23, [x" + r(4) + ", w6, uxtw]",
		"ldrb w24, [x" + r(5) + ", w6, uxtw]",
		"add w7, w7, w21", "add w7, w7, w22", "add w7, w7, w23", "add w7, w7, w24",
		"add w6, w6, #1", "b loop_4",
		"{done_5 0}", "ret",
	}, "\n")
	if got != want {
		t.Fatalf("hoisted form:\n%s\nwant:\n%s", got, want)
	}
}

// The register demand a lowering reports covers the chain behind a missed
// value: with no free register at all, a base's `movz; umaddl; add` are
// three wanted registers, not one, so the second lowering reserves enough
// for the whole chain.
func TestHoistInvariantsWantsTheWholeChain(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	index := w(6)
	items := []asm.Item{
		asm.Label{Name: "head_1"},
		ins("mov", w(6), asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(6), asm.Immediate{Value: 16}),
		bc("hs", "done_5"),
		ins("movz", w(10), asm.Immediate{Value: 80}),
		ins("umaddl", x(9), w(2), w(10), x(0)),
		ins("add", x(10), x(9), asm.Immediate{Value: 64}),
		ins("ldrb", w(7), asm.Memory{Base: x(10), Index: &index, Extend: "uxtw"}),
		ins("add", w(6), w(6), w(7)),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	// Every scratch register is mentioned: the pool is empty.
	mentioned := registersNamed(items)
	for r := 9; r <= 17; r++ {
		mentioned[r] = true
	}
	_, taken, changed, wanted := hoistInvariants(items, mentioned, map[string]map[int]bool{}, nil, nil, "trap_3")
	if changed != 0 || wanted != 3 || len(taken) != 0 {
		t.Fatalf("changed %d, wanted %d, taken %v", changed, wanted, taken)
	}
}

// A read of the old name in another block that every path writes first
// does not pin an invariant: the join after two arms (`mov w9, w11` in
// one, `cset w9, lo` in the other) reads their w9, never the element
// base's, so the base hoists (2026-09-22; before, any read outside the
// block refused it).
func TestHoistInvariantsFollowsReachingDefinitions(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	index := w(6)
	items := []asm.Item{
		asm.Label{Name: "head_1"},
		ins("mov", w(6), asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(6), asm.Immediate{Value: 16}),
		bc("hs", "done_5"),
		ins("add", x(9), x(0), asm.Immediate{Value: 32}),
		ins("ldrb", w(7), asm.Memory{Base: x(9), Index: &index, Extend: "uxtw"}),
		ins("cbz", w(7), asm.Symbol{Name: "short_8"}),
		ins("cmp", w(7), asm.Immediate{Value: 3}),
		ins("cset", w(9), asm.Condition{Code: "lo"}),
		ins("b", asm.Symbol{Name: "join_9"}),
		asm.Label{Name: "short_8"},
		ins("mov", w(9), w(11)),
		asm.Label{Name: "join_9"},
		ins("add", w(6), w(6), w(9)),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	out, taken, changed, wanted := hoistInvariants(items, registersNamed(items), map[string]map[int]bool{}, nil, nil, "trap_3")
	if changed != 1 || wanted != 0 || len(taken) != 1 {
		t.Fatalf("changed %d, wanted %d, taken %v", changed, wanted, taken)
	}
	var spelled []string
	for _, item := range out {
		spelled = append(spelled, strings.TrimSpace(fmt.Sprint(item)))
	}
	got := strings.Join(spelled, "\n")
	name := "x" + itoa(taken[0])
	want := strings.Join([]string{
		"{head_1 0}", "mov w6, wzr",
		"add " + name + ", x0, #32",
		"{loop_4 0}", "cmp w6, #16", "b.hs done_5",
		"ldrb w7, [" + name + ", w6, uxtw]",
		"cbz w7, short_8", "cmp w7, #3", "cset w9, lo", "b join_9",
		"{short_8 0}", "mov w9, w11",
		"{join_9 0}", "add w6, w6, w9", "b loop_4",
		"{done_5 0}", "ret",
	}, "\n")
	if got != want {
		t.Fatalf("hoisted form:\n%s\nwant:\n%s", got, want)
	}
}
