package optir

import (
	"fmt"
	"reflect"
	"strings"
	"testing"
)

func simplifyTestCFG(t *testing.T, cfg CFG) (CFG, SCCPRewriteReport) {
	t.Helper()
	evidence, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	result, report, err := SimplifyWithSCCP(cfg, evidence)
	if err != nil {
		t.Fatal(err)
	}
	return result, report
}

func TestSCCPRewriteFoldsConstantsSelectsBranchAndRepairsSSA(t *testing.T) {
	cfg := CFG{
		Name:    "constant_branch",
		Entry:   0,
		Results: []Type{"u32"},
		Facts:   []Fact{{Name: "dead-path", Values: []ValueID{6}, Provenance: "checked"}},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{
				integerConstant(1, "u32", "40"),
				integerConstant(2, "u32", "2"),
				{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u32", Name: "answer", Source: Source{Line: 4}}}, Operands: []ValueID{1, 2}, Facts: []Fact{{Name: "exact", Values: []ValueID{3}, Provenance: "sccp"}}, Source: Source{Line: 4}},
				{Code: OpConstBool, Results: []Value{sccpValue(4, TypeBool)}, Attributes: []Attribute{{Name: AttributeValue, Value: "true"}}},
			}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 4, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
			{ID: 2, Operations: []Operation{integerConstant(6, "u32", "9")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{6}}}},
			{ID: 3, Parameters: []Value{sccpValue(7, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{7}}},
		},
	}
	original := fmt.Sprintf("%#v", cfg)
	first, report := simplifyTestCFG(t, cfg)
	second, secondReport := simplifyTestCFG(t, cfg)
	if got := fmt.Sprintf("%#v", cfg); got != original {
		t.Fatalf("SCCP rewrite mutated its input:\nwant: %s\ngot:  %s", original, got)
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(report, secondReport) {
		t.Fatalf("SCCP rewrite is not deterministic:\nfirst=%#v %+v\nsecond=%#v %+v", first, report, second, secondReport)
	}
	wantReport := SCCPRewriteReport{
		RewrittenValues:      []ValueID{3},
		SimplifiedBranches:   []BlockID{0},
		RemovedUnreachable:   []BlockID{2},
		MergedBlocks:         []BlockMerge{{Into: 0, Removed: 1}, {Into: 0, Removed: 3}},
		DroppedFunctionFacts: 1,
	}
	if !reflect.DeepEqual(report, wantReport) || report.Changes() != 5 {
		t.Fatalf("SCCP rewrite report = %+v, want %+v", report, wantReport)
	}
	if len(first.Blocks) != 1 || first.Blocks[0].Terminator.Kind != TerminatorReturn ||
		!reflect.DeepEqual(first.Blocks[0].Terminator.Values, []ValueID{3}) {
		t.Fatalf("rewritten CFG shape = %#v", first)
	}
	folded := first.Blocks[0].Operations[2]
	if folded.Code != OpConstInt || !reflect.DeepEqual(folded.Attributes, []Attribute{{Name: AttributeValue, Value: "42"}}) ||
		folded.Results[0].Name != "answer" || folded.Results[0].Source.Line != 4 || folded.Source.Line != 4 || len(folded.Facts) != 1 {
		t.Fatalf("constant rewrite did not preserve identity/source/facts: %#v", folded)
	}
	if err := Verify(first); err != nil {
		t.Fatalf("rewritten CFG does not verify: %v", err)
	}
}

func TestSCCPRewriteSelectsTheExactSameTargetEdgeArguments(t *testing.T) {
	cfg := CFG{
		Name:    "same_target",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{
				{Code: OpConstBool, Results: []Value{sccpValue(1, TypeBool)}, Attributes: []Attribute{{Name: AttributeValue, Value: "false"}}},
				integerConstant(2, "u32", "10"), integerConstant(3, "u32", "20"),
			}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1, Arguments: []ValueID{2}}, False: Edge{Target: 1, Arguments: []ValueID{3}}}},
			{ID: 1, Parameters: []Value{sccpValue(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	result, report := simplifyTestCFG(t, cfg)
	if !reflect.DeepEqual(report.SimplifiedBranches, []BlockID{0}) || len(result.Blocks) != 1 ||
		!reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{3}) {
		t.Fatalf("same-target conditional selected wrong SSA arguments: report=%+v cfg=%#v", report, result)
	}
}

func TestSCCPRewritePreservesEffectfulAndAttributedOperations(t *testing.T) {
	cfg := CFG{
		Name:    "closed_only",
		Entry:   0,
		Results: []Type{"u32", "u32", "u32"},
		Blocks: []Block{{ID: 0, Operations: []Operation{
			integerConstant(1, "u32", "1"), integerConstant(2, "u32", "2"),
			{Code: OpIntAdd, Results: []Value{sccpValue(3, "u32")}, Operands: []ValueID{1, 2}, Effects: []Effect{EffectReadMemory}},
			{Code: OpIntAdd, Results: []Value{sccpValue(4, "u32")}, Operands: []ValueID{1, 2}, Attributes: []Attribute{{Name: "extension.mode", Value: "special"}}},
			{Code: OpConstInt, Results: []Value{sccpValue(5, "u32")}, Attributes: []Attribute{{Name: AttributeValue, Value: "3"}, {Name: "extension.mode", Value: "special"}}},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3, 4, 5}}}},
	}
	result, report := simplifyTestCFG(t, cfg)
	wantFingerprint, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	gotFingerprint, err := FingerprintCFG(result)
	if err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 0 || gotFingerprint != wantFingerprint {
		t.Fatalf("SCCP rewrote an effectful or attributed operation: report=%+v cfg=%#v", report, result)
	}
}

func TestSCCPRewriteMergesSinglePredecessorAndRemapsBlockParameters(t *testing.T) {
	cfg := CFG{
		Name:    "merge",
		Entry:   0,
		Results: []Type{"u32"},
		Facts:   []Fact{{Name: "parameter", Values: []ValueID{3}, Provenance: "checked"}},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{sccpValue(1, "u32")}, Operations: []Operation{integerConstant(2, "u32", "1")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{1}}}},
			{ID: 1, Parameters: []Value{sccpValue(3, "u32")}, Operations: []Operation{{Code: OpIntAdd, Results: []Value{sccpValue(4, "u32")}, Operands: []ValueID{3, 2}}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	result, report := simplifyTestCFG(t, cfg)
	if !reflect.DeepEqual(report.MergedBlocks, []BlockMerge{{Into: 0, Removed: 1}}) || len(result.Blocks) != 1 ||
		!reflect.DeepEqual(result.Blocks[0].Operations[1].Operands, []ValueID{1, 2}) ||
		!reflect.DeepEqual(result.Facts[0].Values, []ValueID{1}) {
		t.Fatalf("single-predecessor merge did not repair SSA uses: report=%+v cfg=%#v", report, result)
	}
}

func TestSCCPRewriteBypassesSafeMultiPredecessorTrampoline(t *testing.T) {
	cfg := CFG{
		Name:    "trampoline",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{sccpValue(1, TypeBool), sccpValue(2, TypeBool)}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{integerConstant(3, "u32", "10")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
			{ID: 2, Operations: []Operation{integerConstant(4, "u32", "20"), integerConstant(5, "u32", "30")}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 3, Arguments: []ValueID{4}}, False: Edge{Target: 4, Arguments: []ValueID{5}}}},
			{ID: 3, Parameters: []Value{sccpValue(6, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 4, Arguments: []ValueID{6}}}},
			{ID: 4, Parameters: []Value{sccpValue(7, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{7}}},
		},
	}
	result, report := simplifyTestCFG(t, cfg)
	if !reflect.DeepEqual(report.RemovedTrampolines, []BlockID{3}) || len(result.Blocks) != 4 {
		t.Fatalf("safe trampoline was not removed: report=%+v cfg=%#v", report, result)
	}
	if result.Blocks[1].Terminator.True.Target != 4 || !reflect.DeepEqual(result.Blocks[1].Terminator.True.Arguments, []ValueID{3}) ||
		result.Blocks[2].Terminator.True.Target != 4 || !reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{4}) {
		t.Fatalf("trampoline incoming edges were not substituted: %#v %#v", result.Blocks[1].Terminator, result.Blocks[2].Terminator)
	}
	if err := Verify(result); err != nil {
		t.Fatalf("trampoline-free CFG does not verify: %v", err)
	}
}

func TestSCCPRewriteRejectsStaleEvidence(t *testing.T) {
	cfg := CFG{Name: "stale", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Operations: []Operation{integerConstant(1, "u32", "1")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	evidence, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	evidence.Values[0].Constant.Integer = "2"
	_, _, err = SimplifyWithSCCP(cfg, evidence)
	if err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("stale SCCP evidence was accepted: %v", err)
	}
}
