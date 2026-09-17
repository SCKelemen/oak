package machine

import "github.com/SCKelemen/oak/asm"

// ElideEmptyFrame removes the lowering's stack adjustment when no remaining
// instruction observes the frame. It deliberately recognizes only the exact
// AArch64 prologue/epilogue pair around one return. Any stack argument,
// aggregate frame object, other sp operand, or mismatched adjustment leaves
// the function unchanged. Changed bodies are still checked and verified by
// the native candidate pipeline.
func ElideEmptyFrame(fn *asm.Function) (*asm.Function, int, error) {
	if fn == nil {
		return nil, 0, nil
	}
	unchanged := func() (*asm.Function, int, error) { return cloneFunction(fn), 0, nil }
	if (fn.Arch != "" && fn.Arch != asm.ArchArm64) || fn.Frame <= 0 || fn.StackArgs != 0 || len(fn.FrameObjects) != 0 {
		return unchanged()
	}
	lifted, err := Lift(cloneFunction(fn))
	if err != nil {
		return nil, 0, err
	}
	if len(lifted.Blocks) == 0 || len(lifted.Blocks[0].Instrs) == 0 {
		return unchanged()
	}
	shrink := lifted.Blocks[0].Instrs[0]
	if !exactStackAdjustment(shrink.Asm, "sub", fn.Frame) {
		return unchanged()
	}

	var ret *Instr
	for _, instruction := range lifted.Instrs {
		if !instruction.Ret {
			continue
		}
		if ret != nil {
			return unchanged()
		}
		ret = instruction
	}
	if ret == nil {
		return unchanged()
	}
	retAt := -1
	for i, instruction := range ret.Block.Instrs {
		if instruction == ret {
			retAt = i
			break
		}
	}
	if retAt < 1 {
		return unchanged()
	}
	grow := ret.Block.Instrs[retAt-1]
	if !exactStackAdjustment(grow.Asm, "add", fn.Frame) {
		return unchanged()
	}

	adjustments := map[*Instr]bool{shrink: true, grow: true}
	for _, instruction := range lifted.Instrs {
		if adjustments[instruction] {
			continue
		}
		if instruction.Call {
			return unchanged()
		}
		for _, operand := range instruction.Asm.Operands {
			if operandUsesStackPointer(operand) {
				return unchanged()
			}
		}
	}
	for _, block := range lifted.Blocks {
		kept := block.Instrs[:0]
		for _, instruction := range block.Instrs {
			if !adjustments[instruction] {
				kept = append(kept, instruction)
			}
		}
		block.Instrs = kept
	}
	lifted.reindex()
	lifted.Asm.Items = lifted.Items()
	lifted.Asm.Frame = 0
	return lifted.Asm, 1, nil
}

func exactStackAdjustment(instruction asm.Instruction, mnemonic string, frame int64) bool {
	if !isStackAdjustment(instruction, mnemonic) {
		return false
	}
	immediate := instruction.Operands[2].(asm.Immediate)
	return immediate.Value == frame && immediate.Shift == 0 && !immediate.MSL
}

func operandUsesStackPointer(operand asm.Operand) bool {
	stack := func(register asm.Register) bool { return register.Class == asm.ClassSP }
	switch operand := operand.(type) {
	case asm.Register:
		return stack(operand)
	case asm.Memory:
		return stack(operand.Base) || operand.Index != nil && stack(*operand.Index)
	case asm.RegisterList:
		for _, register := range operand.Regs {
			if stack(register) {
				return true
			}
		}
	case asm.Extended:
		return stack(operand.Reg)
	case asm.Shifted:
		return stack(operand.Reg)
	case asm.TileSlice:
		return stack(operand.Index)
	}
	return false
}
