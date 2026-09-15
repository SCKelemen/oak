package nativegen

import (
	"fmt"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
)

func ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands}
}

func TestMetricsCountsLoopsAndGuards(t *testing.T) {
	x := func(n int) asm.Register { return asm.Register{Text: "x", Num: n} }
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		ins("mov", x(2), x(0)),
		asm.Label{Name: "loop_4"},
		ins("cmp", x(3), x(20)),
		ins("b", asm.Symbol{Name: "done_5"}),
		ins("ldr", x(9), x(19)),
		ins("cbz", x(9), asm.Symbol{Name: "trap_1"}),
		ins("udiv", x(9), x(2), x(9)),
		ins("add", x(2), x(2), x(9)),
		ins("add", x(3), x(3), x(3)),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("mul", x(0), x(2), x(2)),
		ins("bl", asm.Symbol{Name: "helper"}),
		ins("ret"),
		asm.Label{Name: "trap_1"},
		ins("brk"),
	}}
	fn.Items[3] = asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: "done_5"}}}
	m := Metrics(fn)
	want := opt.Metrics{Instructions: 13, Branches: 3, Loads: 1, Calls: 1, Multiplies: 1, Divides: 1, Guards: 1, Loops: 1, LoopInstructions: 8, LoopBranches: 3, LoopLoads: 1, LoopGuards: 1,
		LoopBodies: []opt.LoopMetrics{{Instructions: 8, Branches: 3, Loads: 1, Guards: 1, Stride: 1}}}
	if fmt.Sprint(m) != fmt.Sprint(want) {
		t.Fatalf("metrics\n got %+v\nwant %+v", m, want)
	}
}

func TestMetricsBoundsRemainderLoops(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	imm := func(v int64) asm.Immediate { return asm.Immediate{Value: v} }
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		asm.Label{Name: "loop_1"},
		ins("cmp", w(3), w(9)),
		asm.Instruction{Mnemonic: "b", Cond: "hi", Operands: []asm.Operand{asm.Symbol{Name: "rest_2"}}},
		ins("ldp", w(10), w(11), w(19)),
		ins("add", w(3), w(3), imm(4)),
		ins("b", asm.Symbol{Name: "loop_1"}),
		asm.Label{Name: "rest_2"},
		ins("cmp", w(3), w(20)),
		asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: "done_3"}}},
		ins("ldrb", w(10), w(19)),
		ins("add", w(3), w(3), imm(1)),
		ins("b", asm.Symbol{Name: "rest_2"}),
		asm.Label{Name: "done_3"},
		ins("ret"),
	}}
	m := Metrics(fn)
	if len(m.LoopBodies) != 2 || m.LoopBodies[0].Stride != 4 || m.LoopBodies[0].MaxTrips != 0 || m.LoopBodies[1].Stride != 1 || m.LoopBodies[1].MaxTrips != 3 {
		t.Fatalf("loop bodies %+v", m.LoopBodies)
	}
	plain := opt.Metrics{Instructions: 7, Branches: 2, Loads: 1, Loops: 1, LoopInstructions: 6, LoopBranches: 2, LoopLoads: 1, LoopBodies: []opt.LoopMetrics{{Instructions: 6, Branches: 2, Loads: 1, Stride: 1}}}
	if opt.AArch64Costs.Estimate(m) >= opt.AArch64Costs.Estimate(plain) {
		t.Fatalf("the unrolled body (%.1f) should cost less than the plain loop (%.1f)", opt.AArch64Costs.Estimate(m), opt.AArch64Costs.Estimate(plain))
	}
}

func TestFindingLine(t *testing.T) {
	if line, ok := FindingLine("count_hits:12: element access not admitted"); !ok || line != 12 {
		t.Fatalf("got %d %v", line, ok)
	}
	if _, ok := FindingLine("no line here"); ok {
		t.Fatal("a finding without a line")
	}
	if _, ok := FindingLine("f:x: y"); ok {
		t.Fatal("a finding with a non-numeric line")
	}
}

func TestTransformsToggleTheLane(t *testing.T) {
	registry := Registry()
	if got := len(registry.Transforms()); got != 8 {
		t.Fatalf("%d transforms", got)
	}
	plain := PlainLane(Lane{Arch: asm.ArchArm64, Strength: true, ElideProven: true, GuardLines: map[int]bool{3: true}, ReuseFlags: true, HoistInvariants: true, VectorHomes: true, Reallocate: true, Cleanup: true})
	if plain.Strength || plain.ElideProven || plain.GuardLines != nil || plain.ReuseFlags || plain.HoistInvariants || plain.VectorHomes || plain.Reallocate || plain.Cleanup || !plain.NoReductions {
		t.Fatalf("plain lane %+v keeps a transform on", plain)
	}
	identity := opt.Identity(plain)
	for _, tr := range registry.Transforms() {
		next := tr.Apply(identity)
		if next == nil {
			t.Fatalf("%s did not apply to the arm64 identity", tr.Name())
		}
		if tr.Apply(next) != nil {
			t.Fatalf("%s applied twice", tr.Name())
		}
		lane := PlainLane(next.Config.(Lane))
		if lane.Arch != plain.Arch || lane.Strength || lane.ElideProven || lane.ReuseFlags || lane.HoistInvariants || lane.VectorHomes || lane.Reallocate || lane.Cleanup || !lane.NoReductions {
			t.Fatalf("%s changed more than its switch: %+v", tr.Name(), lane)
		}
	}
	// The rv64 lane has the law-licensed unrolling, check elision, and
	// layer A's strength reduction (nativegen/rewrite.go, both lanes).
	rv := opt.Identity(PlainLane(Lane{Arch: asm.ArchRV64}))
	for _, tr := range registry.Transforms() {
		applied := tr.Apply(rv) != nil
		if applied != (tr.Name() == TransformUnroll || tr.Name() == TransformElide || tr.Name() == TransformStrength) {
			t.Errorf("%s on rv64: applied %v", tr.Name(), applied)
		}
	}
	// Elision refines by the finding's line, once per line.
	elide, _ := registry.Lookup(TransformElide)
	elided := elide.Apply(identity)
	refined, ok := elide.(opt.Refinable).Refine(elided, "f:12: not admitted")
	if !ok || !refined.Config.(Lane).GuardLines[12] || len(GuardLinesKept(refined.Config.(Lane))) != 1 {
		t.Fatalf("refine: %v %+v", ok, refined)
	}
	if _, again := elide.(opt.Refinable).Refine(refined, "f:12: not admitted"); again {
		t.Fatal("refined the same line twice")
	}
	if _, noLine := elide.(opt.Refinable).Refine(refined, "no line"); noLine {
		t.Fatal("refined without a line")
	}
}

func TestMetricsStrideNeedsOneIncrement(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	imm := func(v int64) asm.Immediate { return asm.Immediate{Value: v} }
	// x9 is rounded up (add #7, lsr #3) and compared: not an index with
	// stride 7; w3 counts by one.
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		asm.Label{Name: "loop_1"},
		ins("add", w(9), w(9), imm(7)),
		ins("lsr", w(9), w(9), imm(3)),
		ins("cmp", w(9), w(20)),
		asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: "done_2"}}},
		ins("cmp", w(3), w(21)),
		asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: "done_2"}}},
		ins("add", w(3), w(3), imm(1)),
		ins("b", asm.Symbol{Name: "loop_1"}),
		asm.Label{Name: "done_2"},
		ins("ret"),
	}}
	m := Metrics(fn)
	if len(m.LoopBodies) != 1 || m.LoopBodies[0].Stride != 1 {
		t.Fatalf("loop bodies %+v", m.LoopBodies)
	}
}
