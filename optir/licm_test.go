package optir

import (
	"fmt"
	"reflect"
	"strings"
	"testing"
)

func licmTestCFG() CFG {
	invariantConstant := integerConstant(6, "u32", "2")
	invariantConstant.Facts = []Fact{{Name: "checked.type", Values: []ValueID{6}, Provenance: "checked", Witness: "u32"}}
	invariantAdd := Operation{
		Code:       OpIntAdd,
		Results:    []Value{{ID: 7, Type: "u32", Name: "stride", Source: Source{Context: "licm.oak", Line: 7, Column: 14}}},
		Operands:   []ValueID{1, 6},
		Attributes: []Attribute{{Name: "plan", Value: "generic"}},
		Facts:      []Fact{{Name: "checked.type", Values: []ValueID{7}, Provenance: "checked", Witness: "u32"}},
		Source:     Source{Context: "licm.oak", Line: 7, Column: 7},
	}
	return CFG{
		Name:    "invariant_chain",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{
				ID:         0,
				Parameters: []Value{cseTestValue(1, "u32"), cseTestValue(2, "u32")},
				Operations: []Operation{integerConstant(3, "u32", "0")},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{3}}},
			},
			{
				ID:         1,
				Parameters: []Value{cseTestValue(4, "u32")},
				Operations: []Operation{{Code: OpLess, Results: []Value{cseTestValue(5, TypeBool)}, Operands: []ValueID{4, 2}}},
				Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 5, True: Edge{Target: 2}, False: Edge{Target: 3, Arguments: []ValueID{4}}},
			},
			{
				ID: 2,
				Operations: []Operation{
					invariantConstant,
					invariantAdd,
					{Code: OpIntAdd, Results: []Value{cseTestValue(8, "u32")}, Operands: []ValueID{4, 7}},
				},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{8}}},
			},
			{ID: 3, Parameters: []Value{cseTestValue(9, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{9}}},
		},
	}
}

func TestHoistLoopInvariantsMovesTotalPureDependencyChain(t *testing.T) {
	cfg := licmTestCFG()
	original := fmt.Sprintf("%#v", cfg)
	first, report, err := HoistLoopInvariants(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, secondReport, err := HoistLoopInvariants(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if got := fmt.Sprintf("%#v", cfg); got != original {
		t.Fatalf("LICM mutated its input:\nwant: %s\ngot:  %s", original, got)
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(report, secondReport) {
		t.Fatalf("LICM is not deterministic:\nfirst:  %#v %+v\nsecond: %#v %+v", first, report, second, secondReport)
	}
	wantMoves := []LICMMove{
		{From: 2, To: 0, Code: OpConstInt, Results: []ValueID{6}},
		{From: 2, To: 0, Code: OpIntAdd, Results: []ValueID{7}},
	}
	if report.LoopsAnalyzed != 1 || report.LoopsWithoutPreheader != 0 || report.HoistedOperations != 2 || !reflect.DeepEqual(report.Moves, wantMoves) {
		t.Fatalf("LICM report = %+v", report)
	}
	if len(first.Blocks[0].Operations) != 3 {
		t.Fatalf("preheader did not preserve operation metadata: %#v", first.Blocks[0])
	}
	moved, originalOperation := first.Blocks[0].Operations[2], cfg.Blocks[2].Operations[1]
	if moved.Code != originalOperation.Code || !reflect.DeepEqual(moved.Results, originalOperation.Results) || !reflect.DeepEqual(moved.Operands, originalOperation.Operands) || !reflect.DeepEqual(moved.Attributes, originalOperation.Attributes) || !reflect.DeepEqual(moved.Facts, originalOperation.Facts) || moved.Source != originalOperation.Source || len(moved.Effects) != 0 {
		t.Fatalf("preheader did not preserve operation metadata: %#v", moved)
	}
	if len(first.Blocks[2].Operations) != 1 || first.Blocks[2].Operations[0].Results[0].ID != 8 {
		t.Fatalf("variant update moved from loop: %#v", first.Blocks[2])
	}
	if err := Verify(first); err != nil {
		t.Fatalf("LICM output does not verify: %v", err)
	}
}

func TestHoistLoopInvariantsKeepsUnlicensedOperationsAndFacts(t *testing.T) {
	tests := []struct {
		name   string
		mutate func(*CFG)
	}{
		{
			name: "potentially trapping division",
			mutate: func(cfg *CFG) {
				cfg.Blocks[2].Operations[1].Code = OpIntDiv
			},
		},
		{
			name: "explicit effect",
			mutate: func(cfg *CFG) {
				cfg.Blocks[2].Operations[1].Effects = []Effect{EffectReadMemory}
			},
		},
		{
			name: "unknown operation",
			mutate: func(cfg *CFG) {
				cfg.Blocks[2].Operations[1].Code = "vendor.unknown"
			},
		},
		{
			name: "path-local fact",
			mutate: func(cfg *CFG) {
				cfg.Blocks[2].Operations[1].Facts = []Fact{{Name: "guarded", Values: []ValueID{7, 4}, Provenance: "branch"}}
			},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := licmTestCFG()
			test.mutate(&cfg)
			result, report, err := HoistLoopInvariants(cfg)
			if err != nil {
				t.Fatal(err)
			}
			if report.HoistedOperations != 1 || len(report.Moves) != 1 || !reflect.DeepEqual(report.Moves[0].Results, []ValueID{6}) {
				t.Fatalf("unlicensed operation moved: %+v", report)
			}
			if len(result.Blocks[2].Operations) != 2 || result.Blocks[2].Operations[0].Results[0].ID != 7 || result.Blocks[2].Operations[1].Results[0].ID != 8 {
				t.Fatalf("loop body = %#v", result.Blocks[2].Operations)
			}
		})
	}
}

func TestHoistLoopInvariantsRequiresCanonicalPreheader(t *testing.T) {
	cfg := licmTestCFG()
	cfg.Blocks[0].Parameters = append(cfg.Blocks[0].Parameters, cseTestValue(10, TypeBool))
	cfg.Blocks[0].Terminator = Terminator{
		Kind:      TerminatorCondBranch,
		Condition: 10,
		True:      Edge{Target: 1, Arguments: []ValueID{3}},
		False:     Edge{Target: 3, Arguments: []ValueID{3}},
	}
	original := fmt.Sprintf("%#v", cfg)
	result, report, err := HoistLoopInvariants(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if got := fmt.Sprintf("%#v", cfg); got != original {
		t.Fatalf("LICM mutated non-canonical input:\nwant: %s\ngot:  %s", original, got)
	}
	if report.LoopsAnalyzed != 1 || report.LoopsWithoutPreheader != 1 || report.HoistedOperations != 0 || len(result.Blocks[0].Operations) != 1 || len(result.Blocks[2].Operations) != 3 {
		t.Fatalf("non-canonical preheader was used: result=%#v report=%+v", result, report)
	}
}

func TestHoistLoopInvariantsMovesNestedInvariantDirectlyOutsideOuterLoop(t *testing.T) {
	cfg := CFG{
		Name:    "nested_invariant",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{cseTestValue(1, "u32"), cseTestValue(2, TypeBool), cseTestValue(3, TypeBool)}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 2}, False: Edge{Target: 6}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 3, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 3, True: Edge{Target: 4}, False: Edge{Target: 5}}},
			{ID: 4, Operations: []Operation{{Code: OpIntAdd, Results: []Value{cseTestValue(4, "u32")}, Operands: []ValueID{1, 1}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 5, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 6, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
		},
	}
	result, report, err := HoistLoopInvariants(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.LoopsAnalyzed != 2 || report.HoistedOperations != 1 || !reflect.DeepEqual(report.Moves, []LICMMove{{From: 4, To: 0, Code: OpIntAdd, Results: []ValueID{4}}}) {
		t.Fatalf("nested LICM report = %+v", report)
	}
	if len(result.Blocks[0].Operations) != 1 || len(result.Blocks[4].Operations) != 0 {
		t.Fatalf("nested invariant was not moved directly to outer preheader: %#v", result.Blocks)
	}
}

func TestHoistLoopInvariantsRejectsMalformedInput(t *testing.T) {
	cfg := licmTestCFG()
	cfg.Blocks[2].Operations[0].Attributes[0].Value = "not-an-integer"
	_, _, err := HoistLoopInvariants(cfg)
	if err == nil || !strings.Contains(err.Error(), "invalid integer") {
		t.Fatalf("LICM accepted malformed input: %v", err)
	}
}
