package optir

import (
	"reflect"
	"testing"
)

func TestEliminateCongruentBlockParametersThroughDiamondAndFacts(t *testing.T) {
	cfg := CFG{
		Name:    "diamond_phi",
		Entry:   0,
		Results: []Type{"u32"},
		Facts:   []Fact{{Name: "function-equality", Values: []ValueID{3, 2}, Provenance: "checked"}},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, TypeBool), phiTestValue(2, "u32")}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 1,
				True: Edge{Target: 1}, False: Edge{Target: 2},
			}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 3, Parameters: []Value{phiTestValue(3, "u32")}, Operations: []Operation{{
				Code: OpIntAdd, Results: []Value{phiTestValue(4, "u32")}, Operands: []ValueID{3, 3},
				Facts: []Fact{{Name: "parameter-result", Values: []ValueID{3, 4}, Provenance: "proved"}},
			}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	originalFingerprint := fingerprintCFG(cfg)

	first, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, secondReport, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if got := fingerprintCFG(cfg); got != originalFingerprint {
		t.Fatalf("block-parameter cleanup mutated its input: before %s, after %s", originalFingerprint, got)
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(report, secondReport) {
		t.Fatalf("block-parameter cleanup is nondeterministic:\n%#v %+v\n%#v %+v", first, report, second, secondReport)
	}
	if report.EliminatedParameters != 1 || !reflect.DeepEqual(report.Replacements, []ValueReplacement{{From: 3, To: 2}}) {
		t.Fatalf("block-parameter report = %+v", report)
	}
	if len(first.Blocks[3].Parameters) != 0 || len(first.Blocks[1].Terminator.True.Arguments) != 0 || len(first.Blocks[2].Terminator.True.Arguments) != 0 {
		t.Fatalf("diamond parameter or edge arguments remain: %#v", first.Blocks)
	}
	operation := first.Blocks[3].Operations[0]
	if !reflect.DeepEqual(operation.Operands, []ValueID{2, 2}) ||
		!reflect.DeepEqual(operation.Facts[0].Values, []ValueID{2, 4}) ||
		!reflect.DeepEqual(first.Facts[0].Values, []ValueID{2, 2}) {
		t.Fatalf("parameter uses or facts were not remapped: operation=%#v facts=%#v", operation, first.Facts)
	}
	if err := Verify(first); err != nil {
		t.Fatalf("cleaned diamond does not verify: %v", err)
	}

	idempotent, idempotentReport, err := EliminateCongruentBlockParameters(first)
	if err != nil {
		t.Fatal(err)
	}
	if fingerprintCFG(idempotent) != fingerprintCFG(first) || idempotentReport.EliminatedParameters != 0 || len(idempotentReport.Replacements) != 0 {
		t.Fatalf("block-parameter cleanup is not idempotent: %+v %#v", idempotentReport, idempotent)
	}
}

func TestEliminateCongruentBlockParametersHandlesSameTargetConditionalEdges(t *testing.T) {
	cfg := CFG{
		Name:    "same_target_phi",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, TypeBool), phiTestValue(2, "u32")}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 1,
				True:  Edge{Target: 1, Arguments: []ValueID{2}},
				False: Edge{Target: 1, Arguments: []ValueID{2}},
			}},
			{ID: 1, Parameters: []Value{phiTestValue(3, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
	result, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 1 || len(result.Blocks[1].Parameters) != 0 ||
		len(result.Blocks[0].Terminator.True.Arguments) != 0 || len(result.Blocks[0].Terminator.False.Arguments) != 0 ||
		!reflect.DeepEqual(result.Blocks[1].Terminator.Values, []ValueID{2}) {
		t.Fatalf("same-target edges were not updated exactly: %+v %#v", report, result.Blocks)
	}
}

func TestEliminateCongruentBlockParametersFindsLoopInvariantFixedPoint(t *testing.T) {
	cfg := CFG{
		Name:    "loop_invariant_phi",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, "u32"), phiTestValue(2, TypeBool)}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{phiTestValue(10, "u32")}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 2,
				True: Edge{Target: 2}, False: Edge{Target: 3, Arguments: []ValueID{10}},
			}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{10}}}},
			{ID: 3, Parameters: []Value{phiTestValue(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	result, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	want := []ValueReplacement{{From: 4, To: 1}, {From: 10, To: 1}}
	if report.EliminatedParameters != 2 || !reflect.DeepEqual(report.Replacements, want) {
		t.Fatalf("loop fixed-point report = %+v, want %+v", report, want)
	}
	if len(result.Blocks[1].Parameters) != 0 || len(result.Blocks[3].Parameters) != 0 ||
		!reflect.DeepEqual(result.Blocks[3].Terminator.Values, []ValueID{1}) {
		t.Fatalf("loop-invariant parameters remain: %#v", result.Blocks)
	}
	if err := Verify(result); err != nil {
		t.Fatalf("loop fixed-point result does not verify: %v", err)
	}
}

func TestEliminateCongruentBlockParametersKeepsLoopInduction(t *testing.T) {
	cfg := CFG{
		Name:    "loop_induction_phi",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, "u32"), phiTestValue(2, TypeBool)}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{phiTestValue(3, "u32")}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 2,
				True: Edge{Target: 2}, False: Edge{Target: 3},
			}},
			{ID: 2, Operations: []Operation{
				phiIntegerConstant(4, "1"),
				{Code: OpIntAdd, Results: []Value{phiTestValue(5, "u32")}, Operands: []ValueID{3, 4}},
			}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{5}}}},
			{ID: 3, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
	result, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 0 || len(result.Blocks[1].Parameters) != 1 || fingerprintCFG(result) != fingerprintCFG(cfg) {
		t.Fatalf("loop induction was eliminated: %+v %#v", report, result.Blocks)
	}
}

func TestEliminateCongruentBlockParametersKeepsEntryParametersAcrossBackedges(t *testing.T) {
	cfg := CFG{
		Name: "entry_loop_parameters", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, "u32"), phiTestValue(2, "u32"), phiTestValue(3, TypeBool)}, Terminator: Terminator{
				Kind: TerminatorCondBranch, Condition: 3,
				True: Edge{Target: 1}, False: Edge{Target: 2},
			}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 0, Arguments: []ValueID{2, 2, 3}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}},
		},
	}
	result, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 0 || fingerprintCFG(result) != fingerprintCFG(cfg) {
		t.Fatalf("ABI entry parameters were inferred from an incomplete backedge input set: %+v %#v", report, result)
	}
}

func TestEliminateCongruentBlockParametersDoesNotGlobalizePathEquality(t *testing.T) {
	cfg := CFG{
		Name:    "path_local_values",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, TypeBool)}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{phiIntegerConstant(2, "7")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Operations: []Operation{phiIntegerConstant(3, "7")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
			{ID: 3, Parameters: []Value{phiTestValue(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	result, report, err := EliminateCongruentBlockParameters(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedParameters != 0 || len(report.Replacements) != 0 || fingerprintCFG(result) != fingerprintCFG(cfg) {
		t.Fatalf("path-local equal expressions became a global equality: %+v %#v", report, result)
	}
}

func TestSimplifyGVNDCEUsesBlockParameterCongruenceBeforeGVN(t *testing.T) {
	dominating := Operation{Code: OpIntAdd, Results: []Value{phiTestValue(3, "u32")}, Operands: []ValueID{2, 2}}
	duplicate := Operation{Code: OpIntAdd, Results: []Value{phiTestValue(5, "u32")}, Operands: []ValueID{4, 4}}
	cfg := CFG{
		Name:    "phi_exposes_gvn",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, TypeBool), phiTestValue(2, "u32")}, Operations: []Operation{dominating}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 3, Parameters: []Value{phiTestValue(4, "u32")}, Operations: []Operation{duplicate}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	result, report, err := SimplifyGVNDCE(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.BlockParameters.EliminatedParameters != 1 || report.GVN.EliminatedOperations != 1 || report.DCE.EliminatedOperations != 0 {
		t.Fatalf("phi/GVN cleanup report = %+v", report)
	}
	if report.Changes() != 2 {
		t.Fatalf("phi/GVN cleanup changes = %d, want 2", report.Changes())
	}
	if len(result.Blocks[3].Parameters) != 0 || len(result.Blocks[3].Operations) != 0 ||
		!reflect.DeepEqual(result.Blocks[3].Terminator.Values, []ValueID{3}) {
		t.Fatalf("phi did not expose global redundancy: %#v", result.Blocks)
	}
}

func TestBlockParameterCongruenceFailsClosedOnDominanceCyclesAndMalformedInput(t *testing.T) {
	parameter := phiTestValue(3, "u32")
	candidate, ok, err := congruentBlockParameterCandidate(
		CFG{Blocks: []Block{
			{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 3, Parameters: []Value{parameter}},
		}},
		3, 0, parameter,
		map[ValueID]definition{2: {typeOf: "u32", block: 1, index: 0}, 3: {typeOf: "u32", block: 3, index: -1}},
		map[BlockID]map[BlockID]bool{3: {0: true, 3: true}},
		nil,
	)
	if err != nil || ok || candidate != 0 {
		t.Fatalf("non-dominating candidate accepted: candidate=%d ok=%v err=%v", candidate, ok, err)
	}
	if _, ok := resolveReplacementBounded(1, map[ValueID]ValueID{1: 2, 2: 1}, 3); ok {
		t.Fatal("cyclic replacement resolved successfully")
	}

	malformed := CFG{
		Name: "malformed_phi", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Parameters: []Value{phiTestValue(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
		},
	}
	if _, _, err := EliminateCongruentBlockParameters(malformed); err == nil {
		t.Fatal("malformed stale edge arity was accepted")
	}
	valid := CFG{
		Name: "stale_parameter", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{phiTestValue(1, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{phiTestValue(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
		},
	}
	if err := removeCongruentBlockParameter(&valid, 1, 0, 99, 1); err == nil {
		t.Fatal("stale block parameter identity was accepted")
	}
}

func phiTestValue(id ValueID, typ Type) Value {
	return Value{ID: id, Type: typ}
}

func phiIntegerConstant(id ValueID, value string) Operation {
	return Operation{
		Code: OpConstInt, Results: []Value{phiTestValue(id, "u32")},
		Attributes: []Attribute{{Name: AttributeValue, Value: value}},
	}
}
