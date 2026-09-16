package optir

import (
	"reflect"
	"strings"
	"testing"
)

func rematerializationTestCFG() CFG {
	return CFG{
		Name: "remat", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32", Name: "x"}},
			Operations: []Operation{
				{Code: OpConstInt, Results: []Value{{ID: 2, Type: "u32"}}, Attributes: []Attribute{{Name: AttributeValue, Value: "41"}}},
				{Code: OpCopy, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{2}},
				{Code: OpIntAdd, Results: []Value{{ID: 4, Type: "u32"}}, Operands: []ValueID{1, 3}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
		}},
	}
}

func TestAnalyzeRematerializationSelectsClosedConstantCopyChain(t *testing.T) {
	cfg := rematerializationTestCFG()
	pool, fixed := []int{0}, map[ValueID]int{1: 0}
	registers, err := PlanRegisters(cfg, pool, fixed)
	if err != nil {
		t.Fatal(err)
	}
	if registers.Spills[2] == 0 || registers.Spills[3] == 0 {
		t.Fatalf("test requires the constant/copy chain to spill: %+v", registers.Spills)
	}
	plan, err := AnalyzeRematerialization(cfg, pool, fixed, registers)
	if err != nil {
		t.Fatal(err)
	}
	want := []RematerializationDecision{
		{Value: 2, Code: OpConstInt, Cost: 1, Uses: 1},
		{Value: 3, Code: OpCopy, Dependencies: []ValueID{2}, Cost: 2, Uses: 1},
	}
	if !reflect.DeepEqual(plan.Decisions, want) {
		t.Fatalf("decisions = %+v, want %+v", plan.Decisions, want)
	}
	if plan.CFGFingerprint == "" || plan.RegisterFingerprint == "" {
		t.Fatalf("missing evidence fingerprints: %+v", plan)
	}
	if err := VerifyRematerializationPlan(cfg, pool, fixed, registers, plan); err != nil {
		t.Fatalf("generated plan does not verify: %v", err)
	}
	again, err := AnalyzeRematerialization(cfg, pool, fixed, registers)
	if err != nil || !reflect.DeepEqual(plan, again) {
		t.Fatalf("analysis is not deterministic: err=%v\nfirst=%+v\nagain=%+v", err, plan, again)
	}
}

func TestVerifyRematerializationRejectsStaleForgedAndCyclicEvidence(t *testing.T) {
	cfg := rematerializationTestCFG()
	pool, fixed := []int{0}, map[ValueID]int{1: 0}
	registers, err := PlanRegisters(cfg, pool, fixed)
	if err != nil {
		t.Fatal(err)
	}
	newPlan := func(t *testing.T) RematerializationPlan {
		t.Helper()
		plan, err := AnalyzeRematerialization(cfg, pool, fixed, registers)
		if err != nil {
			t.Fatal(err)
		}
		return plan
	}

	t.Run("stale CFG", func(t *testing.T) {
		changed := cfg
		changed.Blocks = append([]Block(nil), cfg.Blocks...)
		changed.Blocks[0].Operations = append([]Operation(nil), cfg.Blocks[0].Operations...)
		changed.Blocks[0].Operations[0].Attributes = []Attribute{{Name: AttributeValue, Value: "40"}}
		if err := VerifyRematerializationPlan(changed, pool, fixed, registers, newPlan(t)); err == nil || !strings.Contains(err.Error(), "CFG fingerprint is stale") {
			t.Fatalf("error = %v", err)
		}
	})

	t.Run("stale allocation", func(t *testing.T) {
		forged := registers
		forged.LiveOut = map[BlockID][]ValueID{0: {999}}
		if err := VerifyRematerializationPlan(cfg, pool, fixed, forged, newPlan(t)); err == nil {
			t.Fatal("stale register evidence was accepted")
		}
	})

	t.Run("forged call", func(t *testing.T) {
		plan := newPlan(t)
		plan.Decisions[0].Code = OpCall
		if err := VerifyRematerializationPlan(cfg, pool, fixed, registers, plan); err == nil {
			t.Fatal("forged call rematerialization was accepted")
		}
	})

	t.Run("dependency cycle", func(t *testing.T) {
		plan := newPlan(t)
		plan.Decisions[0].Dependencies = []ValueID{3}
		plan.Decisions[1].Dependencies = []ValueID{2}
		if err := VerifyRematerializationPlan(cfg, pool, fixed, registers, plan); err == nil || !strings.Contains(err.Error(), "cycle") {
			t.Fatalf("error = %v", err)
		}
	})
}

func TestAnalyzeRematerializationRefusesFactsArithmeticAndEffects(t *testing.T) {
	cfg := rematerializationTestCFG()
	cfg.Blocks[0].Operations[0].Facts = []Fact{{Name: "path", Values: []ValueID{2}, Provenance: "test"}}
	pool, fixed := []int{0}, map[ValueID]int{1: 0}
	registers, err := PlanRegisters(cfg, pool, fixed)
	if err != nil {
		t.Fatal(err)
	}
	plan, err := AnalyzeRematerialization(cfg, pool, fixed, registers)
	if err != nil {
		t.Fatal(err)
	}
	for _, decision := range plan.Decisions {
		if decision.Value == 2 || decision.Value == 3 || decision.Value == 4 {
			t.Fatalf("fact-dependent/arithmetic value was rematerialized: %+v", decision)
		}

	}

	effectful := CFG{
		Name: "effect", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{ID: 0, Parameters: []Value{{ID: 1, Type: "u32", Name: "x"}}, Operations: []Operation{
			{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Operands: []ValueID{1}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}}},
			{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{1, 2}},
		}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}}},
	}
	effectRegisters, err := PlanRegisters(effectful, pool, fixed)
	if err != nil {
		t.Fatal(err)
	}
	effectPlan, err := AnalyzeRematerialization(effectful, pool, fixed, effectRegisters)
	if err != nil {
		t.Fatal(err)
	}
	for _, decision := range effectPlan.Decisions {
		if decision.Value == 2 {
			t.Fatalf("call was rematerialized: %+v", decision)
		}
	}
}
