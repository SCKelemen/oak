package machine

import (
	"fmt"
	"math"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// Keep every materialized spill reachable with the base, unsigned-offset
// load/store forms used by this selector. This is also below the unshifted
// immediate limit of the matching sub/add sp pair.
const optIRArm64MaxSpillFrame int64 = 4080

type optIRArm64FrameSlot struct {
	offset    int64
	width     uint8
	alignment uint8
}

type optIRArm64Allocation struct {
	colors  map[optir.ValueID]int
	spills  map[optir.ValueID]optir.SpillSlotID
	slots   map[optir.SpillSlotID]optIRArm64FrameSlot
	frame   int64
	liveOut map[optir.BlockID][]optir.ValueID
}

// optIRArm64Allocate preserves the strict coloring path byte-for-byte. Only a
// pressure refusal constructs and independently verifies an abstract spill
// plan using a pool that leaves three caller-saved scratch registers outside
// the allocator.
func optIRArm64Allocate(cfg optir.CFG, types map[optir.ValueID]optir.Type, fixed map[optir.ValueID]int) (optIRArm64Allocation, error) {
	coloring, strictErr := optir.ColorRegisters(cfg, optIRArm64Registers, fixed)
	if strictErr == nil {
		return optIRArm64Allocation{colors: coloring.Colors, liveOut: coloring.LiveOut}, nil
	}
	plan, err := optir.PlanRegisters(cfg, optIRArm64SpillRegisters, fixed)
	if err != nil {
		return optIRArm64Allocation{}, fmt.Errorf("strict coloring: %v; spill planning: %w", strictErr, err)
	}
	if err := optir.VerifyRegisterPlan(cfg, optIRArm64SpillRegisters, fixed, plan); err != nil {
		return optIRArm64Allocation{}, fmt.Errorf("spill plan evidence: %w", err)
	}
	slots, frame, err := optIRArm64LayoutSpills(plan.Slots)
	if err != nil {
		return optIRArm64Allocation{}, err
	}
	checkLocation := func(value optir.ValueID) error {
		typ, exists := types[value]
		if !exists {
			return fmt.Errorf("value %d has no recorded type", value)
		}
		if typ == optir.Type("()") {
			return nil
		}
		_, colored := plan.Colors[value]
		slot, spilled := plan.Spills[value]
		if colored == spilled {
			return fmt.Errorf("value %d does not have exactly one materialized location", value)
		}
		if spilled {
			if _, exists := slots[slot]; !exists {
				return fmt.Errorf("value %d names missing materialized spill slot %d", value, slot)
			}
		}
		return nil
	}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			if err := checkLocation(parameter.ID); err != nil {
				return optIRArm64Allocation{}, err
			}
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				if err := checkLocation(result.ID); err != nil {
					return optIRArm64Allocation{}, err
				}
			}
		}
	}
	return optIRArm64Allocation{colors: plan.Colors, spills: plan.Spills, slots: slots, frame: frame, liveOut: plan.LiveOut}, nil
}

func optIRArm64LayoutSpills(abstract []optir.SpillSlot) (map[optir.SpillSlotID]optIRArm64FrameSlot, int64, error) {
	slots := make(map[optir.SpillSlotID]optIRArm64FrameSlot, len(abstract))
	var end int64
	for _, slot := range abstract {
		alignment, width := int64(slot.AlignmentBytes), int64(slot.WidthBytes)
		if slot.ID == 0 || width <= 0 || alignment <= 0 || alignment > 8 || alignment&(alignment-1) != 0 || width != alignment {
			return nil, 0, fmt.Errorf("unsupported abstract spill slot %d layout %d/%d", slot.ID, slot.WidthBytes, slot.AlignmentBytes)
		}
		offset, ok := optIRCheckedAlign(end, alignment)
		if !ok || offset > math.MaxInt64-width {
			return nil, 0, fmt.Errorf("spill slot %d offset overflow", slot.ID)
		}
		end = offset + width
		if end > optIRArm64MaxSpillFrame {
			return nil, 0, fmt.Errorf("spill frame needs %d bytes (limit %d)", end, optIRArm64MaxSpillFrame)
		}
		if _, duplicate := slots[slot.ID]; duplicate {
			return nil, 0, fmt.Errorf("duplicate abstract spill slot %d", slot.ID)
		}
		slots[slot.ID] = optIRArm64FrameSlot{offset: offset, width: slot.WidthBytes, alignment: slot.AlignmentBytes}
	}
	frame, ok := optIRCheckedAlign(end, 16)
	if !ok || frame > optIRArm64MaxSpillFrame {
		return nil, 0, fmt.Errorf("aligned spill frame needs more than %d bytes", optIRArm64MaxSpillFrame)
	}
	return slots, frame, nil
}

func optIRCheckedAlign(value, alignment int64) (int64, bool) {
	if value < 0 || alignment <= 0 || alignment&(alignment-1) != 0 {
		return 0, false
	}
	mask := alignment - 1
	if value > math.MaxInt64-mask {
		return 0, false
	}
	return (value + mask) &^ mask, true
}

func optIRSP() asm.Register {
	return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1}
}

func (selector *optIRArm64Selector) valueLocation(value optir.ValueID) (optIRValueLocation, error) {
	if register, colored := selector.colors[value]; colored {
		if _, alsoSpilled := selector.spills[value]; alsoSpilled {
			return optIRValueLocation{}, fmt.Errorf("value %d is both colored and spilled", value)
		}
		return optIRValueLocation{register: register}, nil
	}
	if slot, spilled := selector.spills[value]; spilled && slot != 0 {
		if _, exists := selector.slots[slot]; !exists {
			return optIRValueLocation{}, fmt.Errorf("value %d names missing spill slot %d", value, slot)
		}
		return optIRValueLocation{slot: slot}, nil
	}
	return optIRValueLocation{}, fmt.Errorf("value %d has no machine location", value)
}

func (selector *optIRArm64Selector) readValue(value optir.ValueID, scratch, line int) (int, error) {
	location, err := selector.valueLocation(value)
	if err != nil {
		return 0, err
	}
	if location.slot == 0 {
		return location.register, nil
	}
	if err := selector.loadSpill(location.slot, scratch, selector.types[value], line); err != nil {
		return 0, err
	}
	return scratch, nil
}

func (selector *optIRArm64Selector) writeValue(value optir.ValueID, scratch int) (int, error) {
	location, err := selector.valueLocation(value)
	if err != nil {
		return 0, err
	}
	if location.slot != 0 {
		return scratch, nil
	}
	return location.register, nil
}

func (selector *optIRArm64Selector) commitValue(value optir.ValueID, register, line int) error {
	location, err := selector.valueLocation(value)
	if err != nil {
		return err
	}
	if location.slot == 0 {
		if location.register != register {
			return fmt.Errorf("value %d was produced in x%d, want allocated x%d", value, register, location.register)
		}
		return nil
	}
	return selector.storeSpill(location.slot, register, selector.types[value], line)
}

func (selector *optIRArm64Selector) readLocation(location optIRValueLocation, destination int, typ optir.Type, line int) error {
	if location.slot != 0 {
		return selector.loadSpill(location.slot, destination, typ, line)
	}
	selector.move(destination, location.register, optIRBits(typ), line)
	return nil
}

func (selector *optIRArm64Selector) emitLocationMove(move optIRLocationMove, line int) error {
	if move.destination.slot == 0 {
		return selector.readLocation(move.source, move.destination.register, move.typ, line)
	}
	source := move.source.register
	if move.source.slot != 0 {
		source = optIRSpillOperand1
		if err := selector.loadSpill(move.source.slot, source, move.typ, line); err != nil {
			return err
		}
	}
	return selector.storeSpill(move.destination.slot, source, move.typ, line)
}

func (selector *optIRArm64Selector) loadSpill(slotID optir.SpillSlotID, register int, typ optir.Type, line int) error {
	slot, exists := selector.slots[slotID]
	if !exists {
		return fmt.Errorf("load names missing spill slot %d", slotID)
	}
	width, ok := optIRArm64SpillWidth(typ)
	if !ok || width != slot.width || slot.alignment != slot.width {
		return fmt.Errorf("spill slot %d layout %d/%d disagrees with type %s", slotID, slot.width, slot.alignment, typ)
	}
	mnemonic, destination := "ldr", optIRRegister(register, optIRBits(typ))
	switch typ {
	case optir.TypeBool, "u8":
		mnemonic, destination = "ldrb", optIRW(register)
	case "i8":
		mnemonic, destination = "ldrsb", optIRW(register)
	case "u16":
		mnemonic, destination = "ldrh", optIRW(register)
	case "i16":
		mnemonic, destination = "ldrsh", optIRW(register)
	}
	selector.emit(mnemonic, line, destination, asm.Memory{Base: optIRSP(), Offset: slot.offset})
	return nil
}

func (selector *optIRArm64Selector) storeSpill(slotID optir.SpillSlotID, register int, typ optir.Type, line int) error {
	slot, exists := selector.slots[slotID]
	if !exists {
		return fmt.Errorf("store names missing spill slot %d", slotID)
	}
	width, ok := optIRArm64SpillWidth(typ)
	if !ok || width != slot.width || slot.alignment != slot.width {
		return fmt.Errorf("spill slot %d layout %d/%d disagrees with type %s", slotID, slot.width, slot.alignment, typ)
	}
	mnemonic, source := "str", optIRRegister(register, optIRBits(typ))
	switch width {
	case 1:
		mnemonic, source = "strb", optIRW(register)
	case 2:
		mnemonic, source = "strh", optIRW(register)
	}
	selector.emit(mnemonic, line, source, asm.Memory{Base: optIRSP(), Offset: slot.offset})
	return nil
}

func optIRArm64SpillWidth(typ optir.Type) (uint8, bool) {
	if typ == optir.TypeBool {
		return 1, true
	}
	bits, _, ok := optIRArm64Type(typ)
	if !ok || bits < 8 || bits > 64 || bits%8 != 0 {
		return 0, false
	}
	return uint8(bits / 8), true
}
