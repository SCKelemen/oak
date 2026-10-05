package wasm

import (
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func stackValue(id optir.ValueID) optir.Value { return optir.Value{ID: id, Type: "u32"} }

func stackOperation(code string, id optir.ValueID, operands ...optir.ValueID) optir.Operation {
	return optir.Operation{Code: code, Results: []optir.Value{stackValue(id)}, Operands: operands}
}

func stackPlan(cfg optir.CFG) map[optir.ValueID]optir.Operation {
	f := shapeTestFunction(cfg)
	f.planStackExpressions()
	return f.stackDefinitions
}

func TestStackPlanRequiresOneSameBlockUse(t *testing.T) {
	pure := optir.CFG{Name: "pure", Entry: 1, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 1, Parameters: []optir.Value{stackValue(1)}, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{stackValue(2)}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "7"}}},
			stackOperation(optir.OpIntAdd, 3, 1, 2),
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
	}}}
	if err := optir.Verify(pure); err != nil {
		t.Fatal(err)
	}
	plan := stackPlan(pure)
	if len(plan) != 2 || plan[2].Code != optir.OpConstInt || plan[3].Code != optir.OpIntAdd {
		t.Fatal("pure expression tree was not completely planned", plan)
	}

	shared := pure
	shared.Blocks = append([]optir.Block(nil), pure.Blocks...)
	shared.Blocks[0].Operations = append([]optir.Operation(nil), pure.Blocks[0].Operations...)
	shared.Blocks[0].Operations[1] = stackOperation(optir.OpIntAdd, 3, 2, 2)
	plan = stackPlan(shared)
	if _, ok := plan[2]; ok || plan[3].Code != optir.OpIntAdd {
		t.Fatal("shared operand was duplicated by stack planning", plan)
	}

	cross := optir.CFG{Name: "cross", Entry: 1, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 1, Parameters: []optir.Value{stackValue(1)}, Operations: []optir.Operation{stackOperation(optir.OpIntAdd, 2, 1, 1)},
			Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 2}}},
		{ID: 2, Operations: []optir.Operation{stackOperation(optir.OpIntAdd, 3, 2, 1)},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}}},
	}}
	if err := optir.Verify(cross); err != nil {
		t.Fatal(err)
	}
	plan = stackPlan(cross)
	if _, ok := plan[2]; ok || plan[3].Code != optir.OpIntAdd {
		t.Fatal("definition moved across a CFG block", plan)
	}
}

func TestStackPlanRetainsEffectsTrapsAndDivisionOperands(t *testing.T) {
	cfg := optir.CFG{Name: "barriers", Entry: 1, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 1, Parameters: []optir.Value{stackValue(1)}, Operations: []optir.Operation{
			{Code: optir.OpConstInt, Results: []optir.Value{stackValue(2)}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "2"}}},
			{Code: optir.OpConstInt, Results: []optir.Value{stackValue(3)}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "3"}}},
			{Code: optir.OpIntDiv, Results: []optir.Value{stackValue(4)}, Operands: []optir.ValueID{2, 3}, Effects: []optir.Effect{optir.EffectTrap}},
			{Code: "opaque", Results: []optir.Value{stackValue(5)}, Operands: []optir.ValueID{4}, Effects: []optir.Effect{optir.EffectCall}},
			stackOperation(optir.OpIntAdd, 6, 5, 1),
		}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{6}},
	}}}
	if err := optir.Verify(cfg); err != nil {
		t.Fatal(err)
	}
	plan := stackPlan(cfg)
	for _, id := range []optir.ValueID{2, 3, 4, 5} {
		if _, ok := plan[id]; ok {
			t.Fatalf("value %d crossed a trap/effect boundary: %#v", id, plan[id])
		}
	}
	if plan[6].Code != optir.OpIntAdd {
		t.Fatal("independent pure result was not planned", plan)
	}
}

func TestStackPlanMaterializesEdgeValuesBeforePhiWrites(t *testing.T) {
	cfg := forwardTestCFG([]int{2, 2})
	module, err := Emit([]optir.CFG{cfg})
	if err != nil {
		t.Fatal(err)
	}
	if module.ByteValidation == nil || module.TranslationVerified {
		t.Fatal("stackified edge copies bypassed byte admission")
	}
}
