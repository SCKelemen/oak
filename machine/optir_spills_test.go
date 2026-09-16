package machine

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func TestLayoutOptIRRV64SpillsAlignsAndBoundsCanonicalSlots(t *testing.T) {
	plan := optir.RegisterPlan{
		Spills: map[optir.ValueID]optir.SpillSlotID{1: 1, 2: 2, 3: 3},
		Slots: []optir.SpillSlot{
			{ID: 1, WidthBytes: 8, AlignmentBytes: 8, Values: []optir.ValueID{1}},
			{ID: 2, WidthBytes: 4, AlignmentBytes: 4, Values: []optir.ValueID{2}},
			{ID: 3, WidthBytes: 1, AlignmentBytes: 1, Values: []optir.ValueID{3}},
		},
	}
	layout, err := layoutOptIRRV64Spills(plan, nil, 32)
	if err != nil {
		t.Fatal(err)
	}
	if layout.Frame != 16 || layout.Offsets[1] != 0 || layout.Offsets[2] != 8 || layout.Offsets[3] != 12 {
		t.Fatalf("spill layout = %+v, want offsets 0/8/12 in a 16-byte frame", layout)
	}

	plan.Slots = append(plan.Slots, optir.SpillSlot{ID: 4, WidthBytes: 8, AlignmentBytes: 8, Values: []optir.ValueID{4}})
	plan.Spills[4] = 4
	if _, err := layoutOptIRRV64Spills(plan, nil, 16); err == nil || !strings.Contains(err.Error(), "frame limit") {
		t.Fatalf("overflowing spill layout error = %v", err)
	}
}

func TestLayoutOptIRRV64SpillsOmitsOnlyFullyRematerializedSlots(t *testing.T) {
	plan := optir.RegisterPlan{
		Spills: map[optir.ValueID]optir.SpillSlotID{1: 1, 2: 1, 3: 2},
		Slots: []optir.SpillSlot{
			{ID: 1, WidthBytes: 4, AlignmentBytes: 4, Values: []optir.ValueID{1, 2}},
			{ID: 2, WidthBytes: 4, AlignmentBytes: 4, Values: []optir.ValueID{3}},
		},
	}
	rematerialized := map[optir.ValueID]optir.RematerializationDecision{
		1: {Value: 1, Code: optir.OpConstInt},
		3: {Value: 3, Code: optir.OpConstInt},
	}
	layout, err := layoutOptIRRV64Spills(plan, rematerialized, 32)
	if err != nil {
		t.Fatal(err)
	}
	offset, retained := layout.Offsets[1]
	if layout.Frame != 16 || !retained || offset != 0 {
		t.Fatalf("filtered spill layout = %+v, want shared slot 1 retained at offset zero", layout)
	}
	if _, exists := layout.Offsets[2]; exists {
		t.Fatalf("fully rematerialized slot 2 was physically allocated: %+v", layout)
	}

	rematerialized[2] = optir.RematerializationDecision{Value: 2, Code: optir.OpConstInt}
	layout, err = layoutOptIRRV64Spills(plan, rematerialized, 32)
	if err != nil || layout.Frame != 0 || len(layout.Offsets) != 0 {
		t.Fatalf("fully rematerialized layout = %+v, err=%v; want empty frame", layout, err)
	}
	rematerialized[99] = optir.RematerializationDecision{Value: 99, Code: optir.OpConstInt}
	if _, err := layoutOptIRRV64Spills(plan, rematerialized, 32); err == nil || !strings.Contains(err.Error(), "is not spilled") {
		t.Fatalf("unspilled rematerialization error = %v", err)
	}
}

func TestOptIRRV64RematerializationCostMatchesEncoderWords(t *testing.T) {
	constant := func(typ optir.Type, value string) optir.Operation {
		return optir.Operation{
			Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: typ}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}},
		}
	}
	for name, test := range map[string]struct {
		operation optir.Operation
		cost      uint64
	}{
		"small":    {operation: constant("u32", "2047"), cost: 1},
		"lui only": {operation: constant("u32", "4096"), cost: 1},
		"two word": {operation: constant("u32", "2048"), cost: 2},
		"wide":     {operation: constant("u64", "1311768467463790320"), cost: 6},
		"bool": {operation: optir.Operation{
			Code: optir.OpConstBool, Results: []optir.Value{{ID: 1, Type: optir.TypeBool}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "true"}},
		}, cost: 1},
	} {
		t.Run(name, func(t *testing.T) {
			cost, ok := optIRRV64RematerializationCost(test.operation)
			if !ok || cost != test.cost {
				t.Fatalf("cost = %d, ok=%t; want %d/true", cost, ok, test.cost)
			}
		})
	}
	malformed := constant("u32", "1")
	malformed.Attributes = append(malformed.Attributes, optir.Attribute{Name: "extra", Value: "forged"})
	if _, ok := optIRRV64RematerializationCost(malformed); ok {
		t.Fatal("constant with extra attributes received an RV64 rematerialization cost")
	}
}

func TestOptIRRV64SpillAdmissionAllowsAcyclicCFGAndRejectsCyclesEffectsAndScratchAliasing(t *testing.T) {
	plan := optir.RegisterPlan{Spills: map[optir.ValueID]optir.SpillSlotID{1: 1}}
	branching := optir.CFG{Name: "branching", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.TypeBool}}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 1}, False: optir.Edge{Target: 1}}},
		{ID: 1, Parameters: []optir.Value{{ID: 2, Type: "u32"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}}},
	}}
	if err := validateOptIRRV64SpillCFG(branching, plan); err != nil {
		t.Fatalf("acyclic branching spill admission error = %v", err)
	}

	cyclic := optir.CFG{Name: "cyclic", Entry: 0, Blocks: []optir.Block{
		{ID: 0, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1}}},
		{ID: 1, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 0}}},
	}}
	if err := validateOptIRRV64SpillCFG(cyclic, plan); err == nil || !strings.Contains(err.Error(), "unsupported cyclic control flow") {
		t.Fatalf("cyclic spill admission error = %v", err)
	}

	call := optir.CFG{Name: "call", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{{Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	if err := validateOptIRRV64SpillCFG(call, plan); err != nil {
		t.Fatalf("direct-call spill admission error = %v", err)
	}
	call.Blocks[0].Operations[0] = optir.Operation{
		Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectReadMemory},
	}
	if err := validateOptIRRV64SpillCFG(call, plan); err == nil || !strings.Contains(err.Error(), "non-call effects") {
		t.Fatalf("non-call effect spill admission error = %v", err)
	}

	for name, test := range map[string]struct {
		pool, scratch []int
	}{
		"overlap":   {pool: []int{0, 1}, scratch: []int{1, 2}},
		"duplicate": {pool: []int{0, 1}, scratch: []int{2, 2}},
		"one":       {pool: []int{0, 1}, scratch: []int{2}},
	} {
		t.Run(name, func(t *testing.T) {
			if err := validateOptIRRV64SpillScratches(test.pool, test.scratch); err == nil {
				t.Fatal("invalid scratch set was accepted")
			}
		})
	}
}

func TestComposeOptIRRV64FrameBoundsAndSeparatesReturnAddress(t *testing.T) {
	for name, test := range map[string]struct {
		spill, frame, ra int64
		calls            bool
	}{
		"no frame":       {},
		"call only":      {calls: true, frame: 16, ra: 8},
		"spill only":     {spill: 16, frame: 16},
		"spill and call": {spill: 16, calls: true, frame: 32, ra: 24},
		"maximum":        {spill: 2016, calls: true, frame: 2032, ra: 2024},
	} {
		t.Run(name, func(t *testing.T) {
			frame, ra, err := composeOptIRRV64Frame(test.spill, test.calls)
			if err != nil || frame != test.frame || ra != test.ra {
				t.Fatalf("compose frame = %d, ra = %d, err = %v; want %d/%d", frame, ra, err, test.frame, test.ra)
			}
		})
	}
	for _, spill := range []int64{-16, 8, 2032} {
		if _, _, err := composeOptIRRV64Frame(spill, true); err == nil {
			t.Fatalf("invalid spill/call frame %d was accepted", spill)
		}
	}
}
