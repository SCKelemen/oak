package optir

import (
	"reflect"
	"sort"
	"strings"
	"testing"
)

func registerPressureCFG() CFG {
	return CFG{
		Name: "spill_pressure", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Parameters: []Value{
				{ID: 1, Type: "u32", Name: "a"},
				{ID: 2, Type: "u32", Name: "b"},
				{ID: 3, Type: "u32", Name: "c"},
			},
			Operations: []Operation{
				{Code: OpIntAdd, Results: []Value{{ID: 4, Type: "u32"}}, Operands: []ValueID{1, 2}},
				{Code: OpIntAdd, Results: []Value{{ID: 5, Type: "u32"}}, Operands: []ValueID{4, 3}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}},
		}},
	}
}

func TestRegisterSpillPlanResolvesPressureAndPreservesPrecolors(t *testing.T) {
	cfg := registerPressureCFG()
	if _, err := ColorRegisters(cfg, []int{7, 8}, map[ValueID]int{1: 7}); err == nil {
		t.Fatal("strict coloring unexpectedly admitted three simultaneously live parameters")
	}
	plan, err := PlanRegisters(cfg, []int{8, 7, 8}, map[ValueID]int{1: 7})
	if err != nil {
		t.Fatal(err)
	}
	if plan.Colors[1] != 7 {
		t.Fatalf("fixed value changed color: %v", plan.Colors)
	}
	if _, spilled := plan.Spills[1]; spilled {
		t.Fatalf("fixed value was spilled: %v", plan.Spills)
	}
	if len(plan.Spills) == 0 || len(plan.Slots) == 0 {
		t.Fatalf("pressure did not produce a spill: %+v", plan)
	}
	for _, slot := range plan.Slots {
		if slot.WidthBytes != 4 || slot.AlignmentBytes != 4 {
			t.Fatalf("u32 slot layout = %+v", slot)
		}
	}
	if err := VerifyRegisterPlan(cfg, []int{7, 8}, map[ValueID]int{1: 7}, plan); err != nil {
		t.Fatalf("generated plan did not verify: %v", err)
	}
}

func TestRegisterSpillPlanReusesCompatibleNoninterferingSlots(t *testing.T) {
	cfg := CFG{
		Name: "spill_reuse", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				spillConstant(1, "u32", "1"),
				spillConstant(2, "u32", "2"),
				{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u32"}}, Operands: []ValueID{1, 2}},
				spillConstant(4, "u32", "3"),
				spillConstant(5, "u32", "4"),
				{Code: OpIntAdd, Results: []Value{{ID: 6, Type: "u32"}}, Operands: []ValueID{4, 5}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{6}},
		}},
	}
	plan, err := PlanRegisters(cfg, []int{0}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if len(plan.Spills) < 2 {
		t.Fatalf("expected independent pressure spills, got %v", plan.Spills)
	}
	reused := false
	for _, slot := range plan.Slots {
		if len(slot.Values) >= 2 {
			reused = true
			for left, value := range slot.Values {
				for _, other := range slot.Values[left+1:] {
					if containsValue(plan.Interference[value], other) {
						t.Fatalf("interfering values %d and %d reused slot %d", value, other, slot.ID)
					}
				}
			}
		}
	}
	if !reused {
		t.Fatalf("compatible disjoint spills did not reuse a slot: %+v", plan.Slots)
	}
}

func TestRegisterSpillPlanDoesNotReuseIncompatibleSlots(t *testing.T) {
	cfg := CFG{
		Name: "spill_layouts", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0,
			Operations: []Operation{
				spillConstant(1, "u16", "1"),
				spillConstant(2, "u16", "2"),
				{Code: OpIntAdd, Results: []Value{{ID: 3, Type: "u16"}}, Operands: []ValueID{1, 2}},
				spillConstant(4, "u32", "3"),
				spillConstant(5, "u32", "4"),
				{Code: OpIntAdd, Results: []Value{{ID: 6, Type: "u32"}}, Operands: []ValueID{4, 5}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{6}},
		}},
	}
	plan, err := PlanRegisters(cfg, []int{0}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if len(plan.Spills) < 2 || len(plan.Slots) != 2 {
		t.Fatalf("incompatible u16/u32 spills reused storage: spills=%v slots=%+v", plan.Spills, plan.Slots)
	}
	layouts := map[uint8]bool{}
	for _, slot := range plan.Slots {
		layouts[slot.WidthBytes] = true
	}
	if !layouts[2] || !layouts[4] {
		t.Fatalf("slot layouts = %+v", plan.Slots)
	}
}

func TestRegisterSpillPlanIsDeterministic(t *testing.T) {
	cfg := registerPressureCFG()
	want, err := PlanRegisters(cfg, []int{2, 0, 1, 2}, map[ValueID]int{1: 0})
	if err != nil {
		t.Fatal(err)
	}
	for iteration := 0; iteration < 20; iteration++ {
		got, err := PlanRegisters(cfg, []int{2, 0, 1, 2}, map[ValueID]int{1: 0})
		if err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("iteration %d produced a different plan\nwant: %+v\n got: %+v", iteration, want, got)
		}
	}
}

func TestVerifyRegisterSpillPlanRejectsForgedPlans(t *testing.T) {
	cfg := registerPressureCFG()
	fixed := map[ValueID]int{1: 0}
	newPlan := func(t *testing.T) RegisterPlan {
		t.Helper()
		plan, err := PlanRegisters(cfg, []int{0, 1}, fixed)
		if err != nil {
			t.Fatal(err)
		}
		return plan
	}

	t.Run("changed precolor", func(t *testing.T) {
		plan := newPlan(t)
		plan.Colors[1] = 1
		if err := VerifyRegisterPlan(cfg, []int{0, 1}, fixed, plan); err == nil || !strings.Contains(err.Error(), "fixed value 1 changed") {
			t.Fatalf("error = %v", err)
		}
	})

	t.Run("missing assignment", func(t *testing.T) {
		plan := newPlan(t)
		delete(plan.Colors, 1)
		if err := VerifyRegisterPlan(cfg, []int{0, 1}, fixed, plan); err == nil || !strings.Contains(err.Error(), "exactly one") {
			t.Fatalf("error = %v", err)
		}
	})

	t.Run("interfering slot reuse", func(t *testing.T) {
		plan := newPlan(t)
		var spilled ValueID
		var slot SpillSlotID
		for value, assigned := range plan.Spills {
			spilled, slot = value, assigned
			break
		}
		var neighbor ValueID
		for _, candidate := range plan.Interference[spilled] {
			_, precolored := fixed[candidate]
			if _, colored := plan.Colors[candidate]; colored && !precolored {
				neighbor = candidate
				break
			}
		}
		if spilled == 0 || neighbor == 0 {
			t.Fatalf("test needs a spilled value with colored interference: %+v", plan)
		}
		delete(plan.Colors, neighbor)
		plan.Spills[neighbor] = slot
		for index := range plan.Slots {
			if plan.Slots[index].ID == slot {
				plan.Slots[index].Values = append(plan.Slots[index].Values, neighbor)
				sort.Slice(plan.Slots[index].Values, func(i, j int) bool { return plan.Slots[index].Values[i] < plan.Slots[index].Values[j] })
			}
		}
		if err := VerifyRegisterPlan(cfg, []int{0, 1}, fixed, plan); err == nil || !strings.Contains(err.Error(), "interfering spilled values") {
			t.Fatalf("error = %v", err)
		}
	})

	t.Run("stale liveness", func(t *testing.T) {
		plan := newPlan(t)
		plan.LiveOut[0] = append(plan.LiveOut[0], 999)
		if err := VerifyRegisterPlan(cfg, []int{0, 1}, fixed, plan); err == nil || !strings.Contains(err.Error(), "liveness evidence is stale") {
			t.Fatalf("error = %v", err)
		}
	})
}

func TestRegisterSpillPlanFailsClosedOnUnsupportedLayoutAndMalformedCFG(t *testing.T) {
	unsupported := CFG{
		Name: "unsupported", Entry: 0, Results: []Type{"Widget"},
		Blocks: []Block{{ID: 0, Parameters: []Value{{ID: 1, Type: "Widget"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}}}},
	}
	if _, err := PlanRegisters(unsupported, []int{0}, nil); err == nil || !strings.Contains(err.Error(), "no canonical scalar layout") {
		t.Fatalf("unsupported layout error = %v", err)
	}

	malformed := registerPressureCFG()
	malformed.Blocks[0].Parameters[1].ID = 1
	if _, err := PlanRegisters(malformed, []int{0, 1}, nil); err == nil {
		t.Fatal("malformed SSA was accepted")
	}
}

func spillConstant(id ValueID, typ Type, literal string) Operation {
	return Operation{Code: OpConstInt, Results: []Value{{ID: id, Type: typ}}, Attributes: []Attribute{{Name: AttributeValue, Value: literal}}}
}

func containsValue(values []ValueID, target ValueID) bool {
	for _, value := range values {
		if value == target {
			return true
		}
	}
	return false
}
