package optir

import (
	"fmt"
	"reflect"
	"strings"
	"testing"
)

func canonicalLoopCFG(name string, typ Type, initial, bound, step, comparison, update string) CFG {
	updateOperation := Operation{Code: update, Results: []Value{cseTestValue(7, typ)}, Operands: []ValueID{5, 6}}
	return CFG{
		Name:    name,
		Entry:   0,
		Results: []Type{typ},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{integerConstant(1, typ, initial)}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{cseTestValue(2, typ)}, Operations: []Operation{
				integerConstant(3, typ, bound),
				{Code: comparison, Results: []Value{cseTestValue(4, TypeBool)}, Operands: []ValueID{2, 3}},
			}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 4, True: Edge{Target: 2, Arguments: []ValueID{2}}, False: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Parameters: []Value{cseTestValue(5, typ)}, Operations: []Operation{integerConstant(6, typ, step), updateOperation}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{7}}}},
			{ID: 3, Parameters: []Value{cseTestValue(8, typ)}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{8}}},
		},
	}
}

func TestAnalyzeLoopsFindsDominanceNaturalLoopAndExactTripCount(t *testing.T) {
	cfg := canonicalLoopCFG("count_four", "u32", "0", "4", "1", OpLess, OpIntAdd)
	original := fmt.Sprintf("%#v", cfg)
	first, err := AnalyzeLoops(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, err := AnalyzeLoops(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("loop analysis is not deterministic:\nfirst:  %#v\nsecond: %#v", first, second)
	}
	if got := fmt.Sprintf("%#v", cfg); got != original {
		t.Fatalf("loop analysis mutated its input:\nwant: %s\ngot:  %s", original, got)
	}
	if !reflect.DeepEqual(first.BackEdges, []FlowEdge{{From: 2, To: 1}}) || len(first.Loops) != 1 {
		t.Fatalf("loop shape = %+v", first)
	}
	loop := first.Loops[0]
	if loop.Header != 1 || !reflect.DeepEqual(loop.Latches, []BlockID{2}) || !reflect.DeepEqual(loop.Blocks, []BlockID{1, 2}) || !reflect.DeepEqual(loop.Exits, []FlowEdge{{From: 1, To: 3}}) || !loop.HasPreheader || loop.Preheader != 0 || loop.Depth != 1 {
		t.Fatalf("natural loop = %+v", loop)
	}
	if len(loop.Inductions) != 1 {
		t.Fatalf("inductions = %+v", loop.Inductions)
	}
	induction := loop.Inductions[0]
	if induction.HeaderValue != 2 || induction.Initial != 1 || !reflect.DeepEqual(induction.Updates, []ValueID{7}) || induction.Step != "1" || induction.Predicate != 4 || induction.Bound != 3 || induction.Comparison != OpLess || !induction.HasExactTripCount || induction.ExactTripCount != "4" {
		t.Fatalf("induction = %+v", induction)
	}
	wantDominators := []Dominator{
		{Block: 0, Depth: 0},
		{Block: 1, Immediate: 0, HasImmediate: true, Depth: 1},
		{Block: 2, Immediate: 1, HasImmediate: true, Depth: 2},
		{Block: 3, Immediate: 1, HasImmediate: true, Depth: 2},
	}
	if !reflect.DeepEqual(first.Dominators, wantDominators) || len(first.ReversePostOrder) != 4 || first.ReversePostOrder[0] != 0 {
		t.Fatalf("dominance/RPO = %+v / %v", first.Dominators, first.ReversePostOrder)
	}
}

func TestLoopStructureReuseRequiresCheckedTopologyPreservation(t *testing.T) {
	before := canonicalLoopCFG("reuse", "u32", "0", "4", "1", OpLess, OpIntAdd)
	before.Blocks[0].Operations = append(before.Blocks[0].Operations, integerConstant(9, "u32", "99"))
	structure, err := AnalyzeLoopStructure(before)
	if err != nil {
		t.Fatal(err)
	}
	after, _, err := SimplifyCSEDCE(before)
	if err != nil {
		t.Fatal(err)
	}
	beforeKey := aspectTestKey("cfg.v0", "before")
	afterKey := aspectTestKey("cfg.v1", "after")
	certificate, err := CheckCFGPreservation(beforeKey, before, afterKey, after, orderedAnalysisAspects...)
	if err != nil {
		t.Fatal(err)
	}
	reused, err := AnalyzeLoopsWithPreservedStructure(after, structure, certificate)
	if err != nil {
		t.Fatal(err)
	}
	fresh, err := AnalyzeLoops(after)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(reused, fresh) {
		t.Fatalf("reused loop analysis differs from fresh analysis:\nreused: %#v\nfresh:  %#v", reused, fresh)
	}
	if _, err := AnalyzeLoopsWithStructure(after, structure); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("exact-input API admitted old structure: %v", err)
	}

	changedTopology := after
	changedTopology.Blocks = append([]Block(nil), after.Blocks...)
	changedTopology.Blocks[1].Terminator.True, changedTopology.Blocks[1].Terminator.False = changedTopology.Blocks[1].Terminator.False, changedTopology.Blocks[1].Terminator.True
	changedCertificate, err := CheckCFGPreservation(beforeKey, before, afterKey, changedTopology, orderedAnalysisAspects...)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := AnalyzeLoopsWithPreservedStructure(changedTopology, structure, changedCertificate); err == nil || !strings.Contains(err.Error(), "does not satisfy") {
		t.Fatalf("topology-changing certificate admitted reuse: %v", err)
	}

	mutated := structure
	mutated.ReversePostOrder = append([]BlockID(nil), structure.ReversePostOrder...)
	mutated.ReversePostOrder[0] = 99
	if _, err := AnalyzeLoopsWithPreservedStructure(after, mutated, certificate); err == nil || !strings.Contains(err.Error(), "mutated") {
		t.Fatalf("mutated loop structure admitted reuse: %v", err)
	}
}

func TestAnalyzeLoopsTripCountRespectsDirectionZeroTripsAndWrapping(t *testing.T) {
	tests := []struct {
		name      string
		cfg       CFG
		wantExact bool
		wantCount string
		wantStep  string
	}{
		{name: "zero trip", cfg: canonicalLoopCFG("zero", "u32", "5", "4", "1", OpLess, OpIntAdd), wantExact: true, wantCount: "0", wantStep: "1"},
		{name: "inclusive", cfg: canonicalLoopCFG("inclusive", "u8", "0", "4", "2", OpLessEqual, OpIntAdd), wantExact: true, wantCount: "3", wantStep: "2"},
		{name: "descending", cfg: canonicalLoopCFG("down", "u8", "5", "0", "1", OpGreater, OpIntSub), wantExact: true, wantCount: "5", wantStep: "-1"},
		{name: "wrap blocks proof", cfg: canonicalLoopCFG("wrap", "u8", "250", "255", "10", OpLess, OpIntAdd), wantExact: false, wantStep: "10"},
		{name: "inclusive maximum wraps", cfg: canonicalLoopCFG("inclusive_wrap", "u8", "255", "255", "1", OpLessEqual, OpIntAdd), wantExact: false, wantStep: "1"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			analysis, err := AnalyzeLoops(test.cfg)
			if err != nil {
				t.Fatal(err)
			}
			if len(analysis.Loops) != 1 || len(analysis.Loops[0].Inductions) != 1 {
				t.Fatalf("analysis = %+v", analysis)
			}
			induction := analysis.Loops[0].Inductions[0]
			if induction.Step != test.wantStep || induction.HasExactTripCount != test.wantExact || induction.ExactTripCount != test.wantCount {
				t.Fatalf("induction = %+v", induction)
			}
		})
	}
}

func TestAnalyzeLoopsNormalizesPredicateOperandsAndContinuationArm(t *testing.T) {
	t.Run("bound on left", func(t *testing.T) {
		cfg := canonicalLoopCFG("reversed", "u32", "0", "4", "1", OpGreater, OpIntAdd)
		cfg.Blocks[1].Operations[1].Operands = []ValueID{3, 2}
		analysis, err := AnalyzeLoops(cfg)
		if err != nil {
			t.Fatal(err)
		}
		induction := analysis.Loops[0].Inductions[0]
		if induction.Comparison != OpLess || induction.ExactTripCount != "4" {
			t.Fatalf("reversed predicate = %+v", induction)
		}
	})

	t.Run("false arm continues", func(t *testing.T) {
		cfg := canonicalLoopCFG("false_continues", "u32", "0", "4", "1", OpGreaterEqual, OpIntAdd)
		cfg.Blocks[1].Terminator.True, cfg.Blocks[1].Terminator.False = cfg.Blocks[1].Terminator.False, cfg.Blocks[1].Terminator.True
		analysis, err := AnalyzeLoops(cfg)
		if err != nil {
			t.Fatal(err)
		}
		induction := analysis.Loops[0].Inductions[0]
		if induction.Comparison != OpLess || induction.ExactTripCount != "4" {
			t.Fatalf("false-continuation predicate = %+v", induction)
		}
	})
}

func TestAnalyzeLoopsKeepsSymbolicBoundWithoutInventingTripCount(t *testing.T) {
	cfg := canonicalLoopCFG("symbolic", "u32", "0", "4", "1", OpLess, OpIntAdd)
	cfg.Blocks[0].Parameters = []Value{cseTestValue(9, "u32")}
	cfg.Blocks[1].Operations = cfg.Blocks[1].Operations[1:]
	cfg.Blocks[1].Operations[0].Operands[1] = 9
	analysis, err := AnalyzeLoops(cfg)
	if err != nil {
		t.Fatal(err)
	}
	induction := analysis.Loops[0].Inductions[0]
	if induction.Bound != 9 || induction.HasExactTripCount {
		t.Fatalf("symbolic bound induction = %+v", induction)
	}
}

func TestAnalyzeLoopsFindsNestedParentsAndDepths(t *testing.T) {
	cfg := CFG{
		Name:    "nested",
		Entry:   0,
		Results: []Type{TypeBool},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{cseTestValue(1, TypeBool), cseTestValue(2, TypeBool)}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 2}, False: Edge{Target: 6}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 3, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 4}, False: Edge{Target: 5}}},
			{ID: 4, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 5, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 6, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
		},
	}
	analysis, err := AnalyzeLoops(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if len(analysis.Loops) != 2 {
		t.Fatalf("nested loops = %+v", analysis.Loops)
	}
	outer, inner := analysis.Loops[0], analysis.Loops[1]
	if outer.Header != 1 || outer.Depth != 1 || outer.HasParent || !reflect.DeepEqual(outer.Blocks, []BlockID{1, 2, 3, 4, 5}) {
		t.Fatalf("outer loop = %+v", outer)
	}
	if inner.Header != 3 || inner.Depth != 2 || !inner.HasParent || inner.Parent != 1 || !reflect.DeepEqual(inner.Blocks, []BlockID{3, 4}) {
		t.Fatalf("inner loop = %+v", inner)
	}
}

func multiLatchLoopCFG(secondStep string) CFG {
	return CFG{
		Name:    "multi_latch",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{cseTestValue(10, TypeBool)}, Operations: []Operation{integerConstant(1, "u32", "0")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{cseTestValue(2, "u32")}, Operations: []Operation{integerConstant(3, "u32", "4"), {Code: OpLess, Results: []Value{cseTestValue(4, TypeBool)}, Operands: []ValueID{2, 3}}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 4, True: Edge{Target: 2}, False: Edge{Target: 5, Arguments: []ValueID{2}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 10, True: Edge{Target: 3}, False: Edge{Target: 4}}},
			{ID: 3, Operations: []Operation{integerConstant(5, "u32", "1"), {Code: OpIntAdd, Results: []Value{cseTestValue(6, "u32")}, Operands: []ValueID{2, 5}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{6}}}},
			{ID: 4, Operations: []Operation{integerConstant(7, "u32", secondStep), {Code: OpIntAdd, Results: []Value{cseTestValue(8, "u32")}, Operands: []ValueID{2, 7}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{8}}}},
			{ID: 5, Parameters: []Value{cseTestValue(9, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{9}}},
		},
	}
}

func TestAnalyzeLoopsRequiresAllLatchesToAgree(t *testing.T) {
	agree, err := AnalyzeLoops(multiLatchLoopCFG("1"))
	if err != nil {
		t.Fatal(err)
	}
	if len(agree.Loops) != 1 || len(agree.Loops[0].Inductions) != 1 || !reflect.DeepEqual(agree.Loops[0].Inductions[0].Updates, []ValueID{6, 8}) || agree.Loops[0].Inductions[0].ExactTripCount != "4" {
		t.Fatalf("agreeing latches = %+v", agree.Loops)
	}
	disagree, err := AnalyzeLoops(multiLatchLoopCFG("2"))
	if err != nil {
		t.Fatal(err)
	}
	if len(disagree.Loops) != 1 || len(disagree.Loops[0].Inductions) != 0 {
		t.Fatalf("disagreeing latches produced an induction: %+v", disagree.Loops)
	}
}

func TestAnalyzeLoopsRejectsMalformedRecognizedOperation(t *testing.T) {
	cfg := CFG{
		Name:    "malformed_loop_input",
		Entry:   0,
		Results: []Type{"u8"},
		Blocks:  []Block{{ID: 0, Operations: []Operation{integerConstant(1, "u8", "256")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	_, err := AnalyzeLoops(cfg)
	if err == nil || !strings.Contains(err.Error(), "not canonical for u8") {
		t.Fatalf("loop analysis accepted malformed input: %v", err)
	}
}
