package machine

import (
	"fmt"

	"github.com/SCKelemen/oak/optir"
)

// optIRRV64SpillLayout gives a verified abstract spill slot an RV64 frame
// offset. The first RV64 materialization slice owns the whole frame: calls and
// control-flow joins remain refusals until their layouts compose here.
type optIRRV64SpillLayout struct {
	Offsets map[optir.SpillSlotID]int64
	Frame   int64
}

func layoutOptIRRV64Spills(plan optir.RegisterPlan, maximumFrame int64) (optIRRV64SpillLayout, error) {
	layout := optIRRV64SpillLayout{Offsets: map[optir.SpillSlotID]int64{}}
	if len(plan.Spills) == 0 {
		if len(plan.Slots) != 0 {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill plan has slots without spilled values")
		}
		return layout, nil
	}
	if maximumFrame < 16 {
		return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill frame limit %d is smaller than one aligned frame", maximumFrame)
	}

	var next int64
	for index, slot := range plan.Slots {
		if slot.ID != optir.SpillSlotID(index+1) {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slot %d is not canonical", slot.ID)
		}
		width, alignment := int64(slot.WidthBytes), int64(slot.AlignmentBytes)
		if width != 1 && width != 2 && width != 4 && width != 8 || alignment != width {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slot %d has unsupported %d-byte width/%d-byte alignment", slot.ID, width, alignment)
		}
		aligned, ok := checkedAlign(next, alignment)
		if !ok || aligned > maximumFrame-width {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill slots exceed the %d-byte target frame limit", maximumFrame)
		}
		layout.Offsets[slot.ID] = aligned
		next = aligned + width
	}
	frame, ok := checkedAlign(next, 16)
	if !ok || frame == 0 || frame > maximumFrame {
		return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spill frame exceeds the %d-byte target limit", maximumFrame)
	}
	for value, slot := range plan.Spills {
		if _, exists := layout.Offsets[slot]; !exists {
			return optIRRV64SpillLayout{}, fmt.Errorf("machine: OptIR RV64 spilled value %d names missing slot %d", value, slot)
		}
	}
	layout.Frame = frame
	return layout, nil
}

func checkedAlign(value, alignment int64) (int64, bool) {
	if value < 0 || alignment <= 0 || alignment&(alignment-1) != 0 {
		return 0, false
	}
	mask := alignment - 1
	if value > int64(^uint64(0)>>1)-mask {
		return 0, false
	}
	return (value + mask) &^ mask, true
}

func validateOptIRRV64StraightLineSpills(cfg optir.CFG, plan optir.RegisterPlan) error {
	if len(plan.Spills) == 0 {
		return nil
	}
	if len(cfg.Blocks) != 1 || cfg.Blocks[0].ID != cfg.Entry || cfg.Blocks[0].Terminator.Kind != optir.TerminatorReturn {
		return fmt.Errorf("machine: OptIR RV64 spill materialization supports one return-terminated block")
	}
	for _, operation := range cfg.Blocks[0].Operations {
		if operation.Code == optir.OpCall || len(operation.Effects) != 0 {
			return fmt.Errorf("machine: OptIR RV64 spill materialization refuses calls and effects")
		}
	}
	return nil
}

func validateOptIRRV64SpillScratches(pool, scratches []int) error {
	allocated := map[int]bool{}
	for _, register := range pool {
		if register < 0 || allocated[register] {
			return fmt.Errorf("machine: OptIR RV64 allocation pool has invalid register %d", register)
		}
		allocated[register] = true
	}
	if len(scratches) < 2 {
		return fmt.Errorf("machine: OptIR RV64 spill materialization needs two scratch registers")
	}
	seen := map[int]bool{}
	for _, register := range scratches {
		if register < 0 || seen[register] || allocated[register] {
			return fmt.Errorf("machine: OptIR RV64 spill scratch register %d is invalid, duplicate, or allocated", register)
		}
		seen[register] = true
	}
	return nil
}
