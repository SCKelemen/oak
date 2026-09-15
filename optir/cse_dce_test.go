package optir

import (
	"fmt"
	"reflect"
	"strings"
	"testing"
)

func cseTestValue(id ValueID, typ Type) Value {
	return Value{ID: id, Type: typ}
}

func cseTestAdd(result, left, right ValueID) Operation {
	return Operation{Code: OpIntAdd, Results: []Value{cseTestValue(result, "u32")}, Operands: []ValueID{left, right}}
}

func TestGVNEliminatesDominatingExpressionsAndPreservesFacts(t *testing.T) {
	duplicateFact := Fact{Name: "range", Values: []ValueID{4, 1}, Provenance: "proved", Witness: "same result"}
	cfg := CFG{
		Name:    "same_block",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				integerConstant(1, "u32", "7"),
				integerConstant(2, "u32", "7"),
				cseTestAdd(3, 1, 1),
				{Code: OpIntAdd, Results: []Value{cseTestValue(4, "u32")}, Operands: []ValueID{2, 2}, Facts: []Fact{duplicateFact}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
		}},
	}
	original := fmt.Sprintf("%#v", cfg)
	first, report, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, secondReport, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if got := fmt.Sprintf("%#v", cfg); got != original {
		t.Fatalf("GVN mutated its input:\nwant: %s\ngot:  %s", original, got)
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(report, secondReport) {
		t.Fatalf("GVN is not deterministic:\nfirst:  %#v %+v\nsecond: %#v %+v", first, report, second, secondReport)
	}
	wantReplacements := []ValueReplacement{{From: 2, To: 1}, {From: 4, To: 3}}
	if report.EliminatedOperations != 2 || !reflect.DeepEqual(report.Replacements, wantReplacements) {
		t.Fatalf("GVN report = %+v, want replacements %+v", report, wantReplacements)
	}
	if len(first.Blocks[0].Operations) != 2 || !reflect.DeepEqual(first.Blocks[0].Terminator.Values, []ValueID{3}) {
		t.Fatalf("GVN output = %#v", first.Blocks[0])
	}
	facts := first.Blocks[0].Operations[1].Facts
	if len(facts) != 1 || !reflect.DeepEqual(facts[0].Values, []ValueID{3, 1}) {
		t.Fatalf("duplicate facts were not preserved and remapped: %+v", facts)
	}
}

func TestGVNNumbersExpressionsThroughPlainCopies(t *testing.T) {
	cfg := CFG{
		Name:    "copy_congruence",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				integerConstant(1, "u32", "7"),
				integerConstant(2, "u32", "9"),
				cseTestAdd(3, 1, 2),
				{Code: OpCopy, Results: []Value{cseTestValue(4, "u32")}, Operands: []ValueID{1}},
				cseTestAdd(5, 4, 2),
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}},
		}},
	}
	result, report, err := SimplifyGVNDCE(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.GVN.EliminatedOperations != 1 || !reflect.DeepEqual(report.GVN.Replacements, []ValueReplacement{{From: 5, To: 3}}) {
		t.Fatalf("copy-congruent GVN report = %+v", report.GVN)
	}
	if report.DCE.EliminatedOperations != 1 || !reflect.DeepEqual(report.DCE.EliminatedValues, []ValueID{4}) {
		t.Fatalf("copy cleanup report = %+v", report.DCE)
	}
	if len(result.Blocks[0].Operations) != 3 || !reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{3}) {
		t.Fatalf("copy-congruent output = %#v", result.Blocks[0])
	}
	if err := Verify(result); err != nil {
		t.Fatalf("copy-congruent output does not verify: %v", err)
	}
}

func TestGVNCanonicalizesOnlyExactAlgebraicOperandOrders(t *testing.T) {
	cfg := CFG{
		Name:    "algebraic_order",
		Entry:   0,
		Results: []Type{"u32", TypeBool, TypeBool, TypeBool, "u32", "u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{cseTestValue(1, "u32"), cseTestValue(2, "u32")},
			Operations: []Operation{
				cseTestAdd(3, 1, 2),
				cseTestAdd(4, 2, 1),
				{Code: OpEqual, Results: []Value{cseTestValue(5, TypeBool)}, Operands: []ValueID{1, 2}},
				{Code: OpEqual, Results: []Value{cseTestValue(6, TypeBool)}, Operands: []ValueID{2, 1}},
				{Code: OpLess, Results: []Value{cseTestValue(7, TypeBool)}, Operands: []ValueID{1, 2}},
				{Code: OpGreater, Results: []Value{cseTestValue(8, TypeBool)}, Operands: []ValueID{2, 1}},
				{Code: OpLessEqual, Results: []Value{cseTestValue(9, TypeBool)}, Operands: []ValueID{1, 2}},
				{Code: OpGreaterEqual, Results: []Value{cseTestValue(10, TypeBool)}, Operands: []ValueID{2, 1}},
				{Code: OpIntSub, Results: []Value{cseTestValue(11, "u32")}, Operands: []ValueID{1, 2}},
				{Code: OpIntSub, Results: []Value{cseTestValue(12, "u32")}, Operands: []ValueID{2, 1}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4, 6, 8, 10, 11, 12}},
		}},
	}
	result, report, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	want := []ValueReplacement{{From: 4, To: 3}, {From: 6, To: 5}, {From: 8, To: 7}, {From: 10, To: 9}}
	if report.EliminatedOperations != len(want) || !reflect.DeepEqual(report.Replacements, want) {
		t.Fatalf("algebraic GVN report = %+v, want %+v", report, want)
	}
	if len(result.Blocks[0].Operations) != 6 || !reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{3, 5, 7, 9, 11, 12}) {
		t.Fatalf("algebraic GVN output = %#v", result.Blocks[0])
	}
}

func TestGVNCanonicalizesEveryCommutativeScalarOperation(t *testing.T) {
	operations := []string{OpIntAdd, OpIntMul, OpIntAnd, OpIntOr, OpIntXor, OpEqual, OpNotEqual}
	for _, code := range operations {
		t.Run(code, func(t *testing.T) {
			resultType := Type("u32")
			if code == OpEqual || code == OpNotEqual {
				resultType = TypeBool
			}
			cfg := CFG{
				Name:    "commutative_" + code,
				Entry:   0,
				Results: []Type{resultType},
				Blocks: []Block{{
					ID:         0,
					Parameters: []Value{cseTestValue(1, "u32"), cseTestValue(2, "u32")},
					Operations: []Operation{
						{Code: code, Results: []Value{cseTestValue(3, resultType)}, Operands: []ValueID{1, 2}},
						{Code: code, Results: []Value{cseTestValue(4, resultType)}, Operands: []ValueID{2, 1}},
					},
					Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
				}},
			}
			result, report, err := EliminateGlobalValueRedundancies(cfg)
			if err != nil {
				t.Fatal(err)
			}
			if report.EliminatedOperations != 1 || !reflect.DeepEqual(report.Replacements, []ValueReplacement{{From: 4, To: 3}}) || !reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{3}) {
				t.Fatalf("commutative %s result = %+v %#v", code, report, result.Blocks[0])
			}
		})
	}
}

func TestGVNDoesNotNormalizeAttributedOrEffectfulOperations(t *testing.T) {
	cfg := CFG{
		Name:    "closed_normalization",
		Entry:   0,
		Results: []Type{"u32", "u32", "u32", "u32", "u32", "u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{cseTestValue(1, "u32"), cseTestValue(2, "u32")},
			Operations: []Operation{
				{Code: OpIntAdd, Results: []Value{cseTestValue(3, "u32")}, Operands: []ValueID{1, 2}, Attributes: []Attribute{{Name: "extension.left", Value: "true"}}},
				{Code: OpIntAdd, Results: []Value{cseTestValue(4, "u32")}, Operands: []ValueID{2, 1}, Attributes: []Attribute{{Name: "extension.left", Value: "true"}}},
				{Code: OpIntAdd, Results: []Value{cseTestValue(5, "u32")}, Operands: []ValueID{1, 2}, Effects: []Effect{EffectReadMemory}},
				{Code: OpIntAdd, Results: []Value{cseTestValue(6, "u32")}, Operands: []ValueID{1, 2}, Effects: []Effect{EffectReadMemory}},
				{Code: OpCopy, Results: []Value{cseTestValue(7, "u32")}, Operands: []ValueID{1}, Attributes: []Attribute{{Name: "extension.copy", Value: "true"}}},
				cseTestAdd(8, 7, 2),
				cseTestAdd(9, 1, 2),
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3, 4, 5, 6, 8, 9}},
		}},
	}
	result, report, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	wantFingerprint, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	gotFingerprint, err := FingerprintCFG(result)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 0 || gotFingerprint != wantFingerprint {
		t.Fatalf("GVN normalized an attributed or effectful operation: %+v %#v", report, result)
	}
}

func TestGVNUsesDominanceButNotSiblingAvailability(t *testing.T) {
	t.Run("entry dominates both branches", func(t *testing.T) {
		cfg := CFG{
			Name:    "dominating",
			Entry:   0,
			Results: []Type{"u32"},
			Blocks: []Block{
				{ID: 0, Parameters: []Value{cseTestValue(1, TypeBool)}, Operations: []Operation{integerConstant(2, "u32", "5")}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
				{ID: 1, Operations: []Operation{integerConstant(3, "u32", "5")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
				{ID: 2, Operations: []Operation{integerConstant(4, "u32", "5")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{4}}}},
				{ID: 3, Parameters: []Value{cseTestValue(5, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
			},
		}
		result, report, err := EliminateGlobalValueRedundancies(cfg)
		if err != nil {
			t.Fatal(err)
		}
		if report.EliminatedOperations != 2 || len(result.Blocks[1].Operations) != 0 || len(result.Blocks[2].Operations) != 0 {
			t.Fatalf("dominating GVN = %+v, blocks=%#v", report, result.Blocks)
		}
		if !reflect.DeepEqual(result.Blocks[1].Terminator.True.Arguments, []ValueID{2}) || !reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{2}) {
			t.Fatalf("branch arguments were not rewritten: %#v %#v", result.Blocks[1].Terminator, result.Blocks[2].Terminator)
		}
	})

	t.Run("siblings do not dominate", func(t *testing.T) {
		cfg := CFG{
			Name:    "siblings",
			Entry:   0,
			Results: []Type{"u32"},
			Blocks: []Block{
				{ID: 0, Parameters: []Value{cseTestValue(1, TypeBool)}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
				{ID: 1, Operations: []Operation{integerConstant(2, "u32", "5")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
				{ID: 2, Operations: []Operation{integerConstant(3, "u32", "5")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
				{ID: 3, Parameters: []Value{cseTestValue(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
			},
		}
		result, report, err := EliminateGlobalValueRedundancies(cfg)
		if err != nil {
			t.Fatal(err)
		}
		if report.EliminatedOperations != 0 || len(result.Blocks[1].Operations) != 1 || len(result.Blocks[2].Operations) != 1 {
			t.Fatalf("sibling expression was incorrectly shared: %+v blocks=%#v", report, result.Blocks)
		}
	})
}

func TestGVNKeepsDuplicateWhenItsFactCannotMoveToDominator(t *testing.T) {
	cfg := CFG{
		Name:    "fact_scope",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{cseTestValue(1, TypeBool)}, Operations: []Operation{integerConstant(2, "u32", "5")}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{
				integerConstant(3, "u32", "7"),
				{Code: OpConstInt, Results: []Value{cseTestValue(4, "u32")}, Attributes: []Attribute{{Name: AttributeValue, Value: "5"}}, Facts: []Fact{{Name: "relation", Values: []ValueID{4, 3}, Provenance: "proved"}}},
			}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{4}}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 3, Parameters: []Value{cseTestValue(5, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	result, report, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 0 || len(result.Blocks[1].Operations) != 2 {
		t.Fatalf("GVN moved a path-local fact to a dominator: %+v %#v", report, result.Blocks[1])
	}
}

func TestGVNIncludesOrderedAttributesInIdentity(t *testing.T) {
	cfg := CFG{
		Name:    "attributes",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{cseTestValue(1, "u32")},
			Operations: []Operation{
				{Code: OpCopy, Results: []Value{cseTestValue(2, "u32")}, Operands: []ValueID{1}, Attributes: []Attribute{{Name: "a", Value: "1"}, {Name: "b", Value: "2"}}},
				{Code: OpCopy, Results: []Value{cseTestValue(3, "u32")}, Operands: []ValueID{1}, Attributes: []Attribute{{Name: "b", Value: "2"}, {Name: "a", Value: "1"}}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
		}},
	}
	result, report, err := EliminateGlobalValueRedundancies(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 0 || len(result.Blocks[0].Operations) != 2 {
		t.Fatalf("ordered attributes were treated as equal: %+v %#v", report, result.Blocks[0].Operations)
	}
}

func TestDCERemovesTransitivePureChainButKeepsObservableAndUnknownOperations(t *testing.T) {
	cfg := CFG{
		Name:    "dead",
		Entry:   0,
		Results: []Type{"u32"},
		Facts:   []Fact{{Name: "root", Values: []ValueID{2}, Provenance: "checked"}},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{cseTestValue(1, "u32")},
			Operations: []Operation{
				integerConstant(2, "u32", "1"),
				integerConstant(3, "u32", "2"),
				cseTestAdd(4, 2, 3),
				{Code: OpIntMul, Results: []Value{cseTestValue(5, "u32")}, Operands: []ValueID{4, 3}},
				{Code: OpIntDiv, Results: []Value{cseTestValue(6, "u32")}, Operands: []ValueID{1, 2}},
				{Code: OpIntAdd, Results: []Value{cseTestValue(7, "u32")}, Operands: []ValueID{1, 2}, Effects: []Effect{EffectReadMemory}},
				{Code: OpCall, Results: []Value{cseTestValue(8, "u32")}, Operands: []ValueID{1}, Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}}},
				{Code: "extension.unknown", Results: []Value{cseTestValue(9, "u32")}, Operands: []ValueID{1}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	result, report, err := EliminateDeadCode(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 3 || !reflect.DeepEqual(report.EliminatedValues, []ValueID{3, 4, 5}) {
		t.Fatalf("DCE report = %+v", report)
	}
	if len(result.Blocks[0].Operations) != 5 {
		t.Fatalf("DCE retained/removed wrong operations: %#v", result.Blocks[0].Operations)
	}
	wantCodes := []string{OpConstInt, OpIntDiv, OpIntAdd, OpCall, "extension.unknown"}
	for index, want := range wantCodes {
		if result.Blocks[0].Operations[index].Code != want {
			t.Fatalf("operation %d = %s, want %s", index, result.Blocks[0].Operations[index].Code, want)
		}
	}
}

func TestDCEOwnFactsDisappearWithDefinition(t *testing.T) {
	cfg := CFG{
		Name:    "own_facts",
		Entry:   0,
		Results: []Type{"u32"},
		Blocks: []Block{{
			ID:         0,
			Parameters: []Value{cseTestValue(1, "u32")},
			Operations: []Operation{
				{Code: OpConstInt, Results: []Value{cseTestValue(2, "u32")}, Attributes: []Attribute{{Name: AttributeValue, Value: "9"}}, Facts: []Fact{{Name: "checked.type", Values: []ValueID{2}, Provenance: "checked"}}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	result, report, err := EliminateDeadCode(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if report.EliminatedOperations != 1 || len(result.Blocks[0].Operations) != 0 {
		t.Fatalf("a definition was kept alive only by its own fact: %+v %#v", report, result.Blocks[0])
	}
}

func TestGVNDCERefusesMalformedRecognizedOperation(t *testing.T) {
	cfg := CFG{
		Name:    "malformed",
		Entry:   0,
		Results: []Type{"u8"},
		Blocks:  []Block{{ID: 0, Operations: []Operation{integerConstant(1, "u8", "256")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	for name, transform := range map[string]func(CFG) error{
		"GVN": func(cfg CFG) error { _, _, err := EliminateGlobalValueRedundancies(cfg); return err },
		"DCE": func(cfg CFG) error { _, _, err := EliminateDeadCode(cfg); return err },
	} {
		if err := transform(cfg); err == nil || !strings.Contains(err.Error(), "not canonical for u8") {
			t.Fatalf("%s accepted malformed constant: %v", name, err)
		}
	}
}
