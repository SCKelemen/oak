package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// The unrolled reduction's header (docs/spec/94-assembler.md §9 "Loop
// invariants", invariant tests): `cmp wL, #4; b.lo done` reads only the
// length, so it is peeled before the header; `sub w9, wL, #4` feeds the
// slack test and w9 is rewritten by the body's first load, so it is
// hoisted under a new name; the header keeps `cmp wI, wT; b.hi done`, a
// plain run the rotation pass takes.
func TestHoistInvariantExitTests(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	mem := func(base asm.Register, off int64) asm.Memory { return asm.Memory{Base: base, Offset: off} }
	items := []asm.Item{
		asm.Label{Name: "head_1"},
		ins("mov", w(3), asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(20), asm.Immediate{Value: 4}),
		bc("lo", "done_5"),
		ins("sub", w(9), w(20), asm.Immediate{Value: 4}),
		ins("cmp", w(3), w(9)),
		bc("hi", "done_5"),
		ins("add", x(15), x(19), asm.Extended{Reg: w(3), Kind: "uxtw", Amount: 3}),
		ins("ldp", x(9), x(10), mem(x(15), 0)),
		ins("add", x(2), x(2), x(9)),
		ins("add", x(4), x(4), x(10)),
		ins("add", w(3), w(3), asm.Immediate{Value: 4}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	mentioned := registersNamed(items)
	out, taken, changed, wanted := hoistInvariants(items, mentioned, map[string]map[int]bool{}, nil, nil, "trap_3")
	if changed != 1 || wanted != 0 || len(taken) != 1 {
		t.Fatalf("changed %d, wanted %d, taken %v", changed, wanted, taken)
	}
	var spelled []string
	for _, item := range out {
		spelled = append(spelled, strings.TrimSpace(fmt.Sprint(item)))
	}
	got := strings.Join(spelled, "\n")
	name := "w" + itoa(taken[0])
	want := strings.Join([]string{
		"{head_1 0}", "mov w3, wzr",
		"sub " + name + ", w20, #4",  // the slack, hoisted under a new name
		"cmp w20, #4", "b.lo done_5", // peeled: decided once, right before the header
		"{loop_4 0}",
		"cmp w3, " + name, "b.hi done_5", // the header's remaining test
		"add x15, x19, w3, uxtw #3", "ldp x9, x10, [x15]", "add x2, x2, x9", "add x4, x4, x10", "add w3, w3, #4", "b loop_4",
		"{done_5 0}", "ret",
	}, "\n")
	if got != want {
		t.Fatalf("hoisted items:\n%s\nwant:\n%s", got, want)
	}
	// The header keeps its last test even when it is invariant, and a
	// setup whose destination the body reads stays.
	stays := []asm.Item{
		asm.Label{Name: "loop_4"},
		ins("cmp", w(20), asm.Immediate{Value: 4}),
		bc("lo", "done_5"),
		ins("sub", w(9), w(20), asm.Immediate{Value: 4}),
		ins("cmp", w(3), w(9)),
		bc("hi", "done_5"),
		ins("add", x(2), x(2), x(9)),
		ins("add", w(3), w(3), asm.Immediate{Value: 4}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	out, _, _, _ = hoistInvariants(stays, registersNamed(stays), map[string]map[int]bool{}, nil, nil, "trap_3")
	if fmt.Sprint(out[3]) != fmt.Sprint(stays[3]) || fmt.Sprint(out[4]) != fmt.Sprint(stays[4]) {
		t.Errorf("a setup the body reads must stay in the header: %v", out[:6])
	}
	if l, isLabel := out[2].(asm.Label); !isLabel || l.Name != "loop_4" {
		t.Errorf("the invariant test peels alone: %v", out[:6])
	}
}
