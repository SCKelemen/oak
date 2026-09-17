package asm

import "fmt"

// addCallResultSlots includes the stores performed by memory-returned
// callees in a loop's carried frame. The address must be reconstructed
// from invariant frame addresses, not from a value that changes each
// iteration. The call summary still supplies the stored values.
func (x *pathExecutor) addCallResultSlots(shape loopShape, state *symbolicState, slots map[int64]int64) (string, bool) {
	if x.arch == ArchRV64 || x.fn == nil {
		return "", true // RV64 memory-returned calls remain outside the summary.
	}
	var ranges *symbolicState
	for at := shape.bodyStart; at < shape.bodyEnd; at++ {
		instr, ok := x.items[at].(Instruction)
		if !ok || instr.Mnemonic != "bl" || len(instr.Operands) != 1 {
			continue
		}
		sym, ok := instr.Operands[0].(Symbol)
		if !ok {
			continue
		}
		callee, ok := ResolveNativeCallee(x.arch, sym.Name, x.fn.Callees)
		if !ok {
			continue // summarizeCall will refuse an unresolved call.
		}
		comp, ok := x.fn.Composites[typeText(callee.ReturnType)]
		if !ok || comp.Size <= 16 {
			continue
		}
		base, ok := x.loopFrameAddress(shape, state, at, Register{Class: ClassX, Num: 8})
		if !ok {
			return fmt.Sprintf("a call to %s in a loop returning through an area without an invariant frame address", callee.Name.Value), false
		}
		leaves, _, ok := compositeLeaves(x.fn.Composites, typeText(callee.ReturnType), "", 0, nil)
		if !ok {
			return "a memory-returned call in a loop without a result layout", false
		}
		if ranges == nil {
			ranges = &symbolicState{frame: map[int64]frameSlot{}}
			for addr, size := range slots {
				ranges.frame[addr] = frameSlot{value: constTerm(0, int(size)*8), width: int(size)}
			}
		}
		for _, leaf := range leaves {
			if len(leaf.guards) != 0 {
				return "a memory-returned call in a loop holding a union", false
			}
			width := leaf.width
			if width == 1 {
				width = 32 // Bool's C enum cell, as in summarizeCall.
			}
			// storeSlot splits overlaps into disjoint aligned pieces. A
			// callee's narrow field may overlap an explicit wider spill;
			// freshening both overlapping ranges would lose one symbol.
			ranges.storeSlot(base+leaf.offset, constTerm(0, width), int64(width/8))
		}
	}
	if ranges != nil {
		clear(slots)
		for addr, slot := range ranges.frame {
			slots[addr] = int64(slot.width)
		}
	}
	return "", true
}

// loopFrameAddress resolves an address immediately before at. Apart from
// invariant SP and callee-saved bases, it only follows address arithmetic
// within that basic block. Unknown writes, joins and calls stop the walk.
func (x *pathExecutor) loopFrameAddress(shape loopShape, state *symbolicState, at int, reg Register) (int64, bool) {
	last := max(shape.bodyEnd, shape.testEnd) - 1
	if reg.Class == ClassSP {
		for pc := shape.header + 1; pc <= last; pc++ {
			instr, ok := x.items[pc].(Instruction)
			// SP has number -1; the general-register helper's <=18
			// caller-saved test does not apply to it.
			if ok && instr.Mnemonic != "bl" && instr.Mnemonic != "blr" && writesRegisterIn(x.items, pc, pc, reg.Num) {
				return 0, false
			}
		}
		return -state.disp, true
	}
	if reg.Class != ClassX || reg.ZeroRegister() {
		return 0, false
	}
	if reg.Num >= 19 && reg.Num <= 29 && !writesRegisterIn(x.items, shape.header+1, last, reg.Num) {
		if value, bound := state.regs[reg.Num]; bound {
			return frameAddressOf(value)
		}
		return 0, false
	}
	for pc := at - 1; pc >= shape.bodyStart; pc-- {
		instr, ok := x.items[pc].(Instruction)
		if !ok || isConditionalBranch(instr.Mnemonic) || isUnconditionalJump(instr.Mnemonic) {
			return 0, false
		}
		if !writesRegisterIn(x.items, pc, pc, reg.Num) {
			continue
		}
		if len(instr.Operands) < 2 {
			return 0, false
		}
		dest, okDest := instr.Operands[0].(Register)
		src, okSrc := instr.Operands[1].(Register)
		if !okDest || !okSrc || dest.Class != ClassX || dest.Num != reg.Num {
			return 0, false
		}
		offset := int64(0)
		switch {
		case instr.Mnemonic == "mov" && len(instr.Operands) == 2:
		case (instr.Mnemonic == "add" || instr.Mnemonic == "sub") && len(instr.Operands) == 3:
			imm, ok := instr.Operands[2].(Immediate)
			if !ok {
				return 0, false
			}
			offset = imm.Value
			if instr.Mnemonic == "sub" {
				offset = -offset
			}
		default:
			return 0, false
		}
		base, ok := x.loopFrameAddress(shape, state, pc, src)
		return base + offset, ok
	}
	return 0, false
}
