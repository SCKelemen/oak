package optir

import (
	"reflect"
	"testing"
)

func TestEliminateDeadBlockParametersRemovesSameTargetArguments(t *testing.T) {
	cfg := CFG{
		Name: "dead_same_target", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 1,
				True: Edge{Target: 1, Arguments: []ValueID{2, 2}}, False: Edge{Target: 1, Arguments: []ValueID{2, 2}},
			}},
			{ID: 1, Parameters: []Value{{ID: 3, Type: "u32"}, {ID: 4, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
	original := fingerprintCFG(cfg)
	result, report, err := EliminateDeadBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if fingerprintCFG(cfg) != original {
		t.Fatal("dead block-parameter cleanup mutated its input")
	}
	if report.EliminatedParameters != 1 || !reflect.DeepEqual(report.EliminatedValues, []ValueID{4}) {
		t.Fatalf("dead block-parameter report = %+v", report)
	}
	if got := result.Blocks[1].Parameters; len(got) != 1 || got[0].ID != 3 {
		t.Fatalf("remaining block parameters = %+v", got)
	}
	if got := result.Blocks[0].Terminator; !reflect.DeepEqual(got.True.Arguments, []ValueID{2}) || !reflect.DeepEqual(got.False.Arguments, []ValueID{2}) {
		t.Fatalf("same-target edge arguments = %+v", got)
	}
	idempotent, second, err := EliminateDeadBlockParameters(result)
	if err != nil {
		t.Fatal(err)
	}
	if fingerprintCFG(idempotent) != fingerprintCFG(result) || second.EliminatedParameters != 0 || len(second.EliminatedValues) != 0 {
		t.Fatalf("cleanup is not idempotent: %+v %#v", second, idempotent)
	}
}

func TestEliminateDeadBlockParametersFindsForwardingFixedPointAndKeepsEntry(t *testing.T) {
	cfg := CFG{
		Name: "dead_forwarding", Entry: 0,
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: "u32", Name: "abi"}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{{ID: 2, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 2, Arguments: []ValueID{2}}}},
			{ID: 2, Parameters: []Value{{ID: 3, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn}},
		},
	}
	result, report, err := EliminateDeadBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 2 || !reflect.DeepEqual(report.EliminatedValues, []ValueID{2, 3}) {
		t.Fatalf("fixed-point report = %+v", report)
	}
	if len(result.Blocks[0].Parameters) != 1 || len(result.Blocks[0].Terminator.True.Arguments) != 0 || len(result.Blocks[1].Parameters) != 0 || len(result.Blocks[1].Terminator.True.Arguments) != 0 || len(result.Blocks[2].Parameters) != 0 {
		t.Fatalf("forwarding cleanup = %#v", result.Blocks)
	}
}

func TestEliminateDeadBlockParametersPreservesSemanticAndProofUses(t *testing.T) {
	cfg := CFG{
		Name: "live_parameters", Entry: 0, Results: []Type{"u32"},
		Facts: []Fact{{Name: "root", Values: []ValueID{3}, Provenance: "checked"}},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1, 1, 1}}}},
			{ID: 1, Parameters: []Value{{ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}, {ID: 4, Type: "u32"}}, Operations: []Operation{{
				Code: OpCopy, Results: []Value{{ID: 5, Type: "u32"}}, Operands: []ValueID{2},
				Facts: []Fact{{Name: "operation-root", Values: []ValueID{4}, Provenance: "checked"}},
			}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	result, report, err := EliminateDeadBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 0 || fingerprintCFG(result) != fingerprintCFG(cfg) {
		t.Fatalf("live/proof parameters changed: %+v %#v", report, result)
	}
}

func TestDeadBlockParameterCleanupFailsClosedAndFeedsGVNDCE(t *testing.T) {
	malformed := CFG{
		Name: "malformed_dead", Entry: 0,
		Blocks: []Block{
			{ID: 0, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Parameters: []Value{{ID: 1, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn}},
		},
	}
	if _, _, err := EliminateDeadBlockParameters(malformed); err == nil {
		t.Fatal("malformed incoming edge was accepted")
	}
	valid := CFG{Name: "valid", Entry: 0, Blocks: []Block{{ID: 0, Terminator: Terminator{Kind: TerminatorReturn}}}}
	if err := removeDeadBlockParameter(&valid, 0, 0, 1); err == nil {
		t.Fatal("entry block parameter removal was accepted")
	}

	cfg := CFG{
		Name: "cleanup_report", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1, 1}}}},
			{ID: 1, Parameters: []Value{{ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
		},
	}
	result, report, err := SimplifyGVNDCE(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.DeadBlockParameters.EliminatedParameters != 1 || report.BlockParameters.EliminatedParameters != 1 || report.Changes() != 2 || len(result.Blocks[1].Parameters) != 0 {
		t.Fatalf("GVN/DCE dead-parameter integration = %+v %#v", report, result)
	}
}
