package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

func ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands}
}

// The stride is the index's increment — the register a test compares and
// the loop writes only there. A scratch register a guard compares and the
// body reloads before adding a constant is not the stride.
func TestMetricsStrideIsTheInductionVariable(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Num: n} }
	x := func(n int) asm.Register { return asm.Register{Text: "x", Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		asm.Label{Name: "loop_4"},
		ins("cmp", w(4), w(3)),
		bc("hs", "done_5"),
		ins("mov", w(9), w(2)),
		ins("cmp", w(9), w(1)),
		bc("hs", "trap_3"),
		ins("ldr", w(9), x(11)),
		ins("add", x(9), x(9), asm.Immediate{Value: 7}),
		ins("str", x(9), x(12)),
		ins("add", w(4), w(4), asm.Immediate{Value: 2}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
		asm.Label{Name: "trap_3"},
		ins("brk"),
	}}
	m := Metrics(fn)
	if len(m.LoopBodies) != 1 || m.LoopBodies[0].Stride != 2 {
		t.Fatalf("stride: got %+v, want one loop of stride 2 (the index w4, not the reloaded w9)", m.LoopBodies)
	}
}

func TestMetricsSmallerVectorCleanup(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	for _, test := range []struct {
		name                               string
		middleStep, middleReg, middleTrips int
	}{
		{"vector cleanup", 4, 9, 1},
		{"different index", 4, 10, 0},
		{"equal stride", 8, 9, 0},
		{"larger stride", 16, 9, 0},
	} {
		t.Run(test.name, func(t *testing.T) {
			fn := &asm.Function{Arch: asm.ArchArm64}
			for k, step := range []int{8, test.middleStep, 1} {
				reg := 9
				if k == 1 {
					reg = test.middleReg
				}
				label := fmt.Sprintf("loop_%d", k)
				fn.Items = append(fn.Items,
					asm.Label{Name: label},
					ins("cmp", w(reg), w(20)),
					asm.Instruction{Mnemonic: "b", Cond: "hs", Operands: []asm.Operand{asm.Symbol{Name: fmt.Sprintf("loop_%d", k+1)}}},
					ins("add", w(reg), w(reg), asm.Immediate{Value: int64(step)}),
					ins("b", asm.Symbol{Name: label}))
			}
			fn.Items = append(fn.Items, asm.Label{Name: "loop_3"}, ins("ret"))
			metrics := Metrics(fn)
			if len(metrics.LoopBodies) != 3 || metrics.LoopBodies[1].MaxTrips != test.middleTrips {
				t.Fatalf("unexpected cleanup metrics: %+v", metrics.LoopBodies)
			}
			if test.name == "vector cleanup" && metrics.LoopBodies[2].MaxTrips != 3 {
				t.Fatalf("scalar tail lost its bound: %+v", metrics.LoopBodies[2])
			}
		})
	}
}

// A loop inside a loop: the inner loop's items are its own (depth 1,
// outer 1), the outer loop counts the rest.
func TestMetricsNestedLoops(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Num: n} }
	bc := func(cond, target string) asm.Instruction {
		return asm.Instruction{Mnemonic: "b.", Cond: cond, Operands: []asm.Operand{asm.Symbol{Name: target}}}
	}
	fn := &asm.Function{Arch: asm.ArchArm64, Items: []asm.Item{
		asm.Label{Name: "loop_4"},
		ins("cmp", w(5), w(22)),
		bc("hs", "done_5"),
		ins("mov", w(7), w(20)),
		asm.Label{Name: "loop_6"},
		ins("cmp", w(7), w(23)),
		bc("hs", "done_7"),
		ins("ldr", w(9), w(19)),
		ins("add", w(7), w(7), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_6"}),
		asm.Label{Name: "done_7"},
		ins("add", w(5), w(5), asm.Immediate{Value: 1}),
		ins("b", asm.Symbol{Name: "loop_4"}),
		asm.Label{Name: "done_5"},
		ins("ret"),
	}}
	m := Metrics(fn)
	if len(m.LoopBodies) != 2 {
		t.Fatalf("loop bodies %+v", m.LoopBodies)
	}
	outer, inner := m.LoopBodies[0], m.LoopBodies[1]
	if outer.Instructions != 5 || outer.Branches != 2 || outer.Depth != 0 || outer.Outer != 0 {
		t.Errorf("outer loop: %+v, want its own five instructions and two branches at depth 0", outer)
	}
	if inner.Instructions != 5 || inner.Branches != 2 || inner.Loads != 1 || inner.Depth != 1 || inner.Outer != 1 {
		t.Errorf("inner loop: %+v, want five instructions, two branches, one load at depth 1 inside loop 1", inner)
	}
	if m.LoopInstructions != 10 {
		t.Errorf("the loops hold %d instructions, want 10", m.LoopInstructions)
	}
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
	// The stall estimate is the latency model's (machine.StallEstimate,
	// tested with the scheduler); the counts are what this test pins.
	m.Stalls, m.LoopStalls = 0, 0
	for k := range m.LoopBodies {
		m.LoopBodies[k].Stalls = 0
	}
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

func TestConstantLoopTripsThroughSlackTemporary(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	imm := func(v int64) asm.Immediate { return asm.Immediate{Value: v} }
	items := []asm.Item{
		ins("mov", w(3), w(31)),
		asm.Label{Name: "loop_1"},
		ins("movz", w(10), imm(128)),
		ins("cmp", w(10), imm(4)),
		asm.Instruction{Mnemonic: "b", Cond: "lo", Operands: []asm.Operand{asm.Symbol{Name: "done_2"}}},
		ins("movz", w(10), imm(128)),
		ins("sub", w(10), w(10), imm(4)),
		ins("cmp", w(3), w(10)),
		asm.Instruction{Mnemonic: "b", Cond: "hi", Operands: []asm.Operand{asm.Symbol{Name: "done_2"}}},
		ins("add", w(3), w(3), imm(4)),
		ins("b", asm.Symbol{Name: "loop_1"}),
		asm.Label{Name: "done_2"},
		ins("ret"),
	}
	if got := constantLoopTrips(items, 1, 10, 3, 4, map[string]int{"loop_1": 1, "done_2": 11}); got != 32 {
		t.Fatalf("trips = %d, want 32", got)
	}
}

func TestConstantLoopTripsThroughHoistedSlackTemporary(t *testing.T) {
	w := func(n int) asm.Register { return asm.Register{Text: "w", Class: asm.ClassW, Num: n} }
	imm := func(v int64) asm.Immediate { return asm.Immediate{Value: v} }
	items := []asm.Item{
		ins("mov", w(3), w(31)),
		ins("movz", w(13), imm(128)),
		ins("sub", w(16), w(13), imm(4)),
		asm.Label{Name: "loop_1"},
		ins("cmp", w(3), w(16)),
		asm.Instruction{Mnemonic: "b", Cond: "hi", Operands: []asm.Operand{asm.Symbol{Name: "done_2"}}},
		ins("add", w(3), w(3), imm(4)),
		ins("b", asm.Symbol{Name: "loop_1"}),
		asm.Label{Name: "done_2"},
		ins("ret"),
	}
	labels := map[string]int{"loop_1": 3, "done_2": 8}
	if got := constantLoopTrips(items, 3, 7, 3, 4, labels); got != 32 {
		t.Fatalf("hoisted trips = %d, want 32", got)
	}
	written := append([]asm.Item(nil), items...)
	written[6] = ins("add", w(16), w(16), imm(1))
	if got := constantLoopTrips(written, 3, 7, 3, 4, labels); got != 0 {
		t.Fatalf("loop-written bound yielded %d trips", got)
	}
	calling := append([]asm.Item(nil), items...)
	calling[6] = ins("bl", asm.Symbol{Name: "callee"})
	if got := constantLoopTrips(calling, 3, 7, 3, 4, labels); got != 0 {
		t.Fatalf("call-clobbered bound yielded %d trips", got)
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
	if got := len(registry.Transforms()); got != 26 {
		t.Fatalf("%d transforms", got)
	}
	rotate, _ := registry.Lookup(TransformRotate)
	gatedRotate, isGated := rotate.(opt.Gated)
	neutralRotate, hasShape := rotate.(opt.Neutral)
	if !isGated || !gatedRotate.NeedsVerdict() || !hasShape || neutralRotate.ShapeNeutral() {
		t.Fatalf("loop rotation must preserve an unrotated fallback until its changed control shape proves")
	}
	plain := PlainLane(Lane{Arch: asm.ArchArm64, OptIR: &optir.CFG{}, OptIRFingerprint: "cfg", OptIRChanges: 1, UseOptIR: true, Strength: true, ElideProven: true, GuardLines: map[int]bool{3: true}, ReuseFlags: true, HoistInvariants: true, RotateLoops: true, CarryLoopIndices: true, VectorHomes: true, LoopArrayHomes: true, LoopResultHomes: true, Reallocate: true, Cleanup: true, VectorBlocks: true, ShareVectorAddresses: true, MultiplyAdd: true, ValueSelect: true, VectorReductions: true, VectorMaps: true, UnrollConstant: true, UnrollFills: true, Fuse: true, FuseExits: true, Schedule: true})
	if PlainLane(Lane{UnrollVectorMaps: true}).UnrollVectorMaps {
		t.Fatal("plain lane retained map unrolling")
	}
	if PlainLane(Lane{ShareVectorAddresses: true}).ShareVectorAddresses {
		t.Fatal("plain lane retained late address sharing")
	}
	sharing, _ := registry.Lookup(TransformVectorAddresses)
	if gated, ok := sharing.(opt.Gated); !ok || !gated.NeedsVerdict() {
		t.Fatal("late address sharing must require a semantic verdict")
	}
	if plain.UseOptIR || plain.Strength || plain.ElideProven || plain.GuardLines != nil || plain.ReuseFlags || plain.HoistInvariants || plain.RotateLoops || plain.CarryLoopIndices || plain.VectorHomes || plain.LoopArrayHomes || plain.LoopResultHomes || plain.Reallocate || plain.Cleanup || plain.VectorBlocks || plain.ShareVectorAddresses || plain.MultiplyAdd || plain.ValueSelect || plain.VectorReductions || plain.VectorMaps || plain.UnrollConstant || plain.UnrollFills || plain.Fuse || plain.FuseExits || plain.Schedule || !plain.NoReductions {
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
		if lane.Arch != plain.Arch || lane.UseOptIR || lane.Strength || lane.ElideProven || lane.ReuseFlags || lane.HoistInvariants || lane.CarryLoopIndices || lane.VectorHomes || lane.LoopArrayHomes || lane.LoopResultHomes || lane.Reallocate || lane.Cleanup || lane.VectorBlocks || lane.ShareVectorAddresses || lane.MultiplyAdd || lane.ValueSelect || lane.VectorReductions || lane.UnrollConstant || lane.UnrollFills || !lane.NoReductions {
			t.Fatalf("%s changed more than its switch: %+v", tr.Name(), lane)
		}
	}
	// The rv64 lane also has verifier-gated OptIR emission, the law-licensed
	// unrolling, check elision, and layer A's strength reduction
	// (nativegen/rewrite.go, both lanes).
	rv := opt.Identity(PlainLane(Lane{Arch: asm.ArchRV64, OptIR: &optir.CFG{}, OptIRFingerprint: "cfg", OptIRChanges: 1}))
	for _, tr := range registry.Transforms() {
		applied := tr.Apply(rv) != nil
		if applied != (tr.Name() == TransformOptIR || tr.Name() == TransformUnroll || tr.Name() == TransformUnrollFills || tr.Name() == TransformElide || tr.Name() == TransformStrength || tr.Name() == TransformReallocate || tr.Name() == TransformSchedule) {
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

func TestCompileForRefusesMismatchedOptIRFingerprint(t *testing.T) {
	cfg := optir.CFG{Name: "f", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	for _, arch := range []string{asm.ArchArm64, asm.ArchRV64} {
		lane := Lane{Arch: arch, OptIR: &cfg, OptIRFingerprint: "not-the-cfg-fingerprint", OptIRChanges: 1, UseOptIR: true}
		if _, err := CompileFor(lane, nil, nil, nil, nil, nil, nil); err == nil {
			t.Fatalf("mismatched OptIR fingerprint reached %s materialization", arch)
		}
	}
}

func TestOptIRFingerprintRequiresCompleteCheckedMemoryEvidence(t *testing.T) {
	cfg := optir.CFG{Name: "f", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID:         0,
		Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	metadata := optir.RegionMemoryMetadata{}
	memorySSA := optir.RegionMemorySSA{}
	lane := Lane{OptIR: &cfg, OptIRMemory: &metadata, OptIRMemorySSA: &memorySSA}
	if _, err := lane.optIRFingerprint(); err == nil || !strings.Contains(err.Error(), "complete checked evidence") {
		t.Fatalf("incomplete checked memory fingerprint error = %v", err)
	}
	authority := optir.CheckedMemoryAuthority{}
	lane = Lane{OptIR: &cfg, OptIRMemoryAuthority: &authority}
	if _, err := lane.optIRFingerprint(); err == nil || !strings.Contains(err.Error(), "without region metadata") {
		t.Fatalf("one-sided checked memory fingerprint error = %v", err)
	}
}

func TestOptIRFingerprintRequiresCallCertificateExactlyForCallAuthority(t *testing.T) {
	source := optir.Source{Context: "fingerprint-call.oak", Line: 1, Column: 20}
	call, err := optir.NewCheckedMemoryCallRecord(source, "leaf", "leaf-summary")
	if err != nil {
		t.Fatal(err)
	}
	authority, err := optir.NewCheckedMemoryAuthorityWithCalls(nil, []optir.CheckedMemoryCallRecord{call})
	if err != nil {
		t.Fatal(err)
	}
	cfg := optir.CFG{Name: "caller", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0,
		Operations: []optir.Operation{{
			Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "leaf"}}, Source: source, MemoryCallID: call.ID,
		}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	projection, err := optir.ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	lane := Lane{
		OptIR: &cfg, OptIRMemory: &projection.Metadata, OptIRMemorySSA: &memorySSA,
		OptIRMemoryAuthority: &authority, OptIRMemoryProjection: &projection,
	}
	if _, err := lane.optIRFingerprint(); err == nil || !strings.Contains(err.Error(), "without a call certificate") {
		t.Fatalf("missing checked call certificate fingerprint error = %v", err)
	}

	emptyAuthority, err := optir.NewCheckedMemoryAuthority(nil)
	if err != nil {
		t.Fatal(err)
	}
	emptyProjection, err := optir.ProjectCheckedMemory(optir.CFG{Name: "plain", Entry: 0, Blocks: []optir.Block{{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorReturn}}}}, emptyAuthority)
	if err != nil {
		t.Fatal(err)
	}
	emptySSA, err := optir.AnalyzeRegionMemorySSA(optir.CFG{Name: "plain", Entry: 0, Blocks: []optir.Block{{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorReturn}}}}, emptyProjection.Metadata)
	if err != nil {
		t.Fatal(err)
	}
	var unexpected optir.CheckedMemoryCallCertificate
	plainCFG := optir.CFG{Name: "plain", Entry: 0, Blocks: []optir.Block{{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorReturn}}}}
	lane = Lane{
		OptIR: &plainCFG, OptIRMemory: &emptyProjection.Metadata, OptIRMemorySSA: &emptySSA,
		OptIRMemoryAuthority: &emptyAuthority, OptIRMemoryProjection: &emptyProjection,
		OptIRMemoryCallCertificate: &unexpected,
	}
	if _, err := lane.optIRFingerprint(); err == nil || !strings.Contains(err.Error(), "without checked memory call authority") {
		t.Fatalf("unexpected checked call certificate fingerprint error = %v", err)
	}
}
