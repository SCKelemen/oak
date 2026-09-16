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
	layout, err := layoutOptIRRV64Spills(plan, 32)
	if err != nil {
		t.Fatal(err)
	}
	if layout.Frame != 16 || layout.Offsets[1] != 0 || layout.Offsets[2] != 8 || layout.Offsets[3] != 12 {
		t.Fatalf("spill layout = %+v, want offsets 0/8/12 in a 16-byte frame", layout)
	}

	plan.Slots = append(plan.Slots, optir.SpillSlot{ID: 4, WidthBytes: 8, AlignmentBytes: 8, Values: []optir.ValueID{4}})
	plan.Spills[4] = 4
	if _, err := layoutOptIRRV64Spills(plan, 16); err == nil || !strings.Contains(err.Error(), "frame limit") {
		t.Fatalf("overflowing spill layout error = %v", err)
	}
}

func TestOptIRRV64SpillAdmissionRejectsControlFlowEffectsAndScratchAliasing(t *testing.T) {
	plan := optir.RegisterPlan{Spills: map[optir.ValueID]optir.SpillSlotID{1: 1}}
	branching := optir.CFG{Name: "branching", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.TypeBool}}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 1}, False: optir.Edge{Target: 1}}},
		{ID: 1, Parameters: []optir.Value{{ID: 2, Type: "u32"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}}},
	}}
	if err := validateOptIRRV64StraightLineSpills(branching, plan); err == nil || !strings.Contains(err.Error(), "one return-terminated block") {
		t.Fatalf("branching spill admission error = %v", err)
	}

	call := optir.CFG{Name: "call", Entry: 0, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 0, Operations: []optir.Operation{{Code: optir.OpCall, Results: []optir.Value{{ID: 1, Type: "u32"}}, Effects: []optir.Effect{optir.EffectCall}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
	if err := validateOptIRRV64StraightLineSpills(call, plan); err == nil || !strings.Contains(err.Error(), "refuses calls and effects") {
		t.Fatalf("call spill admission error = %v", err)
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
