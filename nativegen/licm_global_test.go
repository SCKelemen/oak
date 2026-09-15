package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// A scalar global's load leaves the loop when the loop stores to no
// global's address (docs/spec/94-assembler.md §9 "Loop invariants"). The
// register that held the global's address is reused for the element base
// of the store: the store is not the global's, and the load — its
// address formed in the loop, straight-line before it — hoists.
func TestHoistScalarGlobalPastReusedAddressRegister(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w" + itoa(n), Class: asm.ClassW, Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x" + itoa(n), Class: asm.ClassX, Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	index := w(4)
	items := []asm.Item{
		asm.Label{Name: "head_1"},
		ins("mov", w(4), asm.Register{Text: "wzr", Class: asm.ClassW, Num: 31}),
		asm.Label{Name: "loop_4"},
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("adrp", x(11), asm.Symbol{Name: "extra"}),
		ins("add", x(11), x(11), asm.Symbol{Name: "extra", Lo12: true}),
		ins("ldr", w(9), asm.Memory{Base: x(11)}),
		ins("add", x(9), x(9), asm.Immediate{Value: 7}),
		ins("add", x(11), x(10), asm.Immediate{Value: 0}),
		ins("str", x(9), asm.Memory{Base: x(11), Index: &index, Shift: 3, Extend: "uxtw"}),
		ins("add", w(4), w(4), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}
	globals := map[string]asm.Global{"extra": {Type: "u32", Bits: 32}}
	out, _, _, wanted := hoistInvariants(items, registersNamed(items), map[string]map[int]bool{}, nil, globals, "trap_3")
	if wanted != 0 {
		t.Fatalf("wanted %d registers", wanted)
	}
	inLoop, loads, addresses := false, 0, 0
	for _, item := range out {
		switch it := item.(type) {
		case asm.Label:
			inLoop = it.Name == "loop_4"
		case asm.Instruction:
			if !inLoop {
				continue
			}
			switch it.Mnemonic {
			case "ldr":
				loads++
			case "adrp":
				addresses++
			}
		}
	}
	if loads != 0 || addresses != 0 {
		t.Fatalf("the global's address and value must leave the loop; %d loads and %d adrp remain:\n%v", loads, addresses, out)
	}
	// The same loop storing through the global's address keeps the load.
	items[10] = ins("str", x(9), asm.Memory{Base: x(11)})
	items[9] = ins("add", x(12), x(10), asm.Immediate{Value: 0})
	out, _, _, _ = hoistInvariants(items, registersNamed(items), map[string]map[int]bool{}, nil, globals, "trap_3")
	inLoop, loads = false, 0
	for _, item := range out {
		switch it := item.(type) {
		case asm.Label:
			inLoop = it.Name == "loop_4"
		case asm.Instruction:
			if inLoop && it.Mnemonic == "ldr" {
				loads++
			}
		}
	}
	if loads != 1 {
		t.Fatalf("a loop storing through the global's address must keep its load; got %d:\n%v", loads, out)
	}
}
