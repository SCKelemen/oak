package optir

import (
	"reflect"
	"testing"
)

func TestAnalyzeBlockLayoutPrefersLoopContinuationAndBackedge(t *testing.T) {
	cfg := CFG{
		Name: "loop_layout", Entry: 0, Results: []Type{TypeBool},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 2}, False: Edge{Target: 3}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 3}}},
			{ID: 3, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
		},
	}
	layout, err := AnalyzeBlockLayout(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyBlockLayout(cfg, layout); err != nil {
		t.Fatal(err)
	}
	wantProbabilities := []BranchProbability{
		{Block: 1, TrueWeight: likelyBranchWeight, FalseWeight: neutralBranchWeight, Reason: BranchLoopStay},
		{Block: 2, TrueWeight: likelyBranchWeight, FalseWeight: neutralBranchWeight, Reason: BranchLoopBackedge},
	}
	if !reflect.DeepEqual(layout.Probabilities, wantProbabilities) {
		t.Fatalf("probabilities = %+v, want %+v", layout.Probabilities, wantProbabilities)
	}
	if want := []BlockID{0, 1, 2, 3}; !reflect.DeepEqual(layout.Order, want) {
		t.Fatalf("order = %v, want %v", layout.Order, want)
	}
}

func TestAnalyzeBlockLayoutKeepsNeutralDiamondsDeterministic(t *testing.T) {
	cfg := CFG{
		Name: "diamond_layout", Entry: 10, Results: []Type{TypeBool},
		Blocks: []Block{
			{ID: 40, Parameters: []Value{{ID: 2, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
			{ID: 30, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 40, Arguments: []ValueID{1}}}},
			{ID: 10, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 30}, False: Edge{Target: 20}}},
			{ID: 20, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 40, Arguments: []ValueID{1}}}},
		},
	}
	first, err := AnalyzeBlockLayout(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, err := AnalyzeBlockLayout(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("layout is nondeterministic:\nfirst  %+v\nsecond %+v", first, second)
	}
	wantProbability := []BranchProbability{{
		Block: 10, TrueWeight: neutralBranchWeight,
		FalseWeight: neutralBranchWeight, Reason: BranchNeutral,
	}}
	if !reflect.DeepEqual(first.Probabilities, wantProbability) {
		t.Fatalf("probabilities = %+v, want %+v", first.Probabilities, wantProbability)
	}
	if want := []BlockID{10, 20, 30, 40}; !reflect.DeepEqual(first.Order, want) {
		t.Fatalf("order = %v, want %v", first.Order, want)
	}

	// The proposal is canonical with respect to CFG block storage order.
	reordered := cfg
	reordered.Blocks = []Block{cfg.Blocks[2], cfg.Blocks[3], cfg.Blocks[1], cfg.Blocks[0]}
	third, err := AnalyzeBlockLayout(reordered)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.Order, third.Order) || !reflect.DeepEqual(first.Probabilities, third.Probabilities) {
		t.Fatalf("block storage order changed layout: first=%+v reordered=%+v", first, third)
	}
}

func TestVerifyBlockLayoutRejectsMutationAndStaleCFG(t *testing.T) {
	cfg := CFG{
		Name: "layout_identity", Entry: 0, Results: []Type{TypeBool},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
		},
	}
	layout, err := AnalyzeBlockLayout(cfg)
	if err != nil {
		t.Fatal(err)
	}
	mutated := layout
	mutated.Order = append([]BlockID(nil), layout.Order...)
	mutated.Order[1], mutated.Order[2] = mutated.Order[2], mutated.Order[1]
	if err := VerifyBlockLayout(cfg, mutated); err == nil {
		t.Fatal("mutated layout was accepted")
	}
	stale := cfg
	stale.Name = "layout_identity_changed"
	if err := VerifyBlockLayout(stale, layout); err == nil {
		t.Fatal("layout from a different CFG was accepted")
	}
}
