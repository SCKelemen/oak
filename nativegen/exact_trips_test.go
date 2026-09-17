package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
)

func exactMetricLoop(rotated bool) *asm.Function {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	branch := func(cond, name string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: name}}}
	}
	items := []asm.Item{ins("movz", w(0), asm.Immediate{}), ins("movz", w(9), asm.Immediate{})}
	if !rotated {
		items = append(items, asm.Label{Name: "loop"})
	}
	items = append(items, ins("cmp", w(9), asm.Immediate{Value: 8}), branch("hs", "done"))
	if rotated {
		items = append(items, asm.Label{Name: "loop"})
	}
	items = append(items, ins("add", w(0), w(0), w(9)), ins("add", w(9), w(9), asm.Immediate{Value: 1}))
	if rotated {
		items = append(items, ins("cmp", w(9), asm.Immediate{Value: 8}), branch("lo", "loop"))
	} else {
		items = append(items, branch("", "loop"))
	}
	items = append(items, asm.Label{Name: "done"}, ins("ret"))
	return &asm.Function{Arch: asm.ArchArm64, Items: items}
}

func TestMetricsExactTripsTopAndRotated(t *testing.T) {
	for _, rotated := range []bool{false, true} {
		m := Metrics(exactMetricLoop(rotated))
		if len(m.LoopBodies) != 1 || m.LoopBodies[0].ExactTrips != 8 || m.LoopBodies[0].MaxTrips != 8 {
			t.Fatalf("rotated=%v: exact count or separate upper bound missing: %+v", rotated, m.LoopBodies)
		}
	}
}

func TestExactLoopMetricRangeRequiresWholeNaturalLoop(t *testing.T) {
	shapes, err := machine.LoopShapes(exactMetricLoop(true))
	if err != nil || len(shapes) != 1 {
		t.Fatalf("loop shape: %v %v", shapes, err)
	}
	shape := shapes[0]
	first := shape.Loop.Header.Instrs[0].Index
	latch := shape.Loop.Latches[0]
	last := latch.Instrs[len(latch.Instrs)-1].Index
	if !exactLoopMetricRange(shape, first, last) {
		t.Fatal("exact natural-loop range refused")
	}
	for _, pair := range [][2]int{{first - 1, last}, {first + 1, last}, {first, last - 1}, {first, last + 1}, {last + 1, first}} {
		if exactLoopMetricRange(shape, pair[0], pair[1]) {
			t.Fatalf("different lexical range inherited exact evidence: %v", pair)
		}
	}
	changed, loop := *shape, *shape.Loop
	changed.Loop = &loop
	loop.Latches = append(loop.Latches, latch)
	if exactLoopMetricRange(&changed, first, last) {
		t.Fatal("multiple backedges inherited one exact range")
	}
	loop.Latches = []*machine.Block{latch}
	loop.Blocks = append(append([]*machine.Block(nil), loop.Blocks...), loop.Header)
	if exactLoopMetricRange(&changed, first, last) {
		t.Fatal("duplicate natural-loop instructions inherited exact evidence")
	}
}
