package machine

import "github.com/SCKelemen/oak/asm"

// exactLoopTrips recognizes a deliberately closed AArch64 loop shape. It
// counts body iterations, not the extra header test of a top-tested loop.
// Unlike MaxTrips, this reads the actual CFG exit: an internal comparison
// against the same index is not necessarily the loop's continuation test.
// This is only a cost hint; it neither rewrites code nor licenses a proof.
func (f *Function) exactLoopTrips(loop *Loop, dom *Dominance, siteWeb map[site]*Web) int {
	if f.t.arch != asm.ArchArm64 || loop.Preheader == nil || len(loop.Latches) != 1 {
		return 0
	}
	header, latch := loop.Header, loop.Latches[0]
	inside := make(map[*Block]bool, len(loop.Blocks))
	for _, block := range loop.Blocks {
		if !dom.Reachable(block) || !dom.Dominates(header, block) {
			return 0
		}
		inside[block] = true
	}
	// Exactly one external edge, no alternate entries, and no terminal or
	// call/system effect which could bypass the counted recurrence. A
	// guard's branch into the trap block is not an exit the count sees: it
	// aborts the function on an invalid input, and every trip runs the
	// guard alike, so a guarded counted loop trips as often as the same
	// loop with its guards proven away — the cost that decides between the
	// two must not read the guard as the loop ending early (the OS page
	// walkers' scans kept their redundant guards on that reading).
	var exitFrom, exitTo *Block
	for _, block := range loop.Blocks {
		for _, pred := range block.Preds {
			if !inside[pred] && (block != header || pred != loop.Preheader) {
				return 0
			}
		}
		if len(block.Succs) == 0 {
			return 0
		}
		for _, succ := range block.Succs {
			if !inside[succ] {
				if isTrapBlock(succ) {
					continue
				}
				if exitFrom != nil {
					return 0
				}
				exitFrom, exitTo = block, succ
			}
		}
		for _, instruction := range block.Instrs {
			if instruction.Call || instruction.Ret || instruction.Trap || (!instruction.Branch && f.t.barrier(instruction)) {
				return 0
			}
		}
	}
	if exitFrom == nil || len(exitFrom.Instrs) < 2 || len(loopSuccessors(exitFrom)) != 2 {
		return 0
	}
	// Removing the unique latch edge must leave a DAG. This excludes child
	// loops and irreducible internal cycles, even if the induction happens
	// to dominate the outer latch.
	colors := make(map[*Block]uint8, len(inside))
	var acyclic func(*Block) bool
	acyclic = func(block *Block) bool {
		if colors[block] == 1 {
			return false
		}
		if colors[block] == 2 {
			return true
		}
		colors[block] = 1
		for _, succ := range block.Succs {
			if !inside[succ] || (block == latch && succ == header) {
				continue
			}
			if !acyclic(succ) {
				return false
			}
		}
		colors[block] = 2
		return true
	}
	if !acyclic(header) || len(colors) != len(inside) {
		return 0
	}
	branch := exitFrom.Instrs[len(exitFrom.Instrs)-1]
	compare := exitFrom.Instrs[len(exitFrom.Instrs)-2]
	if (branch.Asm.Mnemonic != "b" && branch.Asm.Mnemonic != "b.") || len(branch.Asm.Operands) != 1 {
		return 0
	}
	target := f.labels[branchTarget(branch.Asm)]
	top, inclusive := false, false
	switch branch.Asm.Cond {
	case "hs", "hi":
		if exitFrom != header || target != exitTo || len(latch.Succs) != 1 || latch.Succs[0] != header {
			return 0
		}
		top, inclusive = true, branch.Asm.Cond == "hi"
	case "lo", "ls":
		if exitFrom != latch || target != header {
			return 0
		}
		inclusive = branch.Asm.Cond == "ls"
	default:
		return 0
	}
	// Adjacency ensures the branch consumes this compare's flags. Operand
	// shape and width checks below avoid treating shifted immediates or a
	// W/X alias with different arithmetic as the same recurrence.
	if compare.Asm.Mnemonic != "cmp" || len(compare.Asm.Operands) != 2 || len(compare.Uses) != 1 {
		return 0
	}
	bound, immediate := compare.Asm.Operands[1].(asm.Immediate)
	index, register := compare.Asm.Operands[0].(asm.Register)
	if !immediate || bound.Shift != 0 || bound.Value < 0 || !register || (index.Class != asm.ClassW && index.Class != asm.ClassX) || index.ZeroRegister() {
		return 0
	}
	use := compare.Uses[0]
	web := siteWeb[site{compare, use, false}]
	if web == nil || len(web.Defs) != 2 || use.Implicit || use.Op != 0 || use.Part != partReg || use.Bits != viewBits(index) {
		return 0
	}
	var initial, increment *Instr
	for _, definition := range web.Defs {
		if definition.Instr == nil || definition.Access.Implicit || definition.Access.Bits != use.Bits {
			return 0
		}
		if inside[definition.Instr.Block] {
			if increment != nil {
				return 0
			}
			increment = definition.Instr
		} else {
			if initial != nil {
				return 0
			}
			initial = definition.Instr
		}
	}
	if initial == nil || increment == nil || !dom.Dominates(initial.Block, header) || !dom.Dominates(initial.Block, loop.Preheader) || len(initial.Defs) != 1 || initial.Defs[0].Reg != use.Reg {
		return 0
	}
	start, known := f.exactTripStart(initial, index.Class)
	if !known || increment.Asm.Mnemonic != "add" || len(increment.Asm.Operands) != 3 || len(increment.Defs) != 1 || len(increment.Uses) != 1 {
		return 0
	}
	reg, signedStep, adding := f.t.increment(increment.Asm)
	if !adding || signedStep <= 0 || reg != use.Reg || increment.Defs[0].Bits != use.Bits || increment.Uses[0].Bits != use.Bits ||
		siteWeb[site{increment, increment.Defs[0], true}] != web || siteWeb[site{increment, increment.Uses[0], false}] != web {
		return 0
	}
	if !dom.Dominates(increment.Block, latch) || (top && !dom.DominatesInstr(compare, increment)) || (!top && !dom.DominatesInstr(increment, compare)) {
		return 0
	}
	// Even a short-lived write belonging to a different web is refused.
	// The physical induction register has exactly one in-loop definition.
	for _, block := range loop.Blocks {
		for _, instruction := range block.Instrs {
			for _, definition := range instruction.Defs {
				if definition.Reg == use.Reg && instruction != increment {
					return 0
				}
			}
		}
	}
	limit := ^uint64(0)
	if use.Bits == 32 {
		limit = 1<<32 - 1
	}
	boundValue, step := uint64(bound.Value), uint64(signedStep)
	if start > limit || boundValue > limit || step > limit || start > boundValue || (!inclusive && start == boundValue) {
		return 0
	}
	// For a bottom-tested loop this deliberately requires a start which
	// satisfies the continuation bound. Whether a preheader skips entry
	// does not change the positive count for executions which enter it.
	distance := boundValue - start
	if inclusive {
		distance++ // bound is a nonnegative int64, so this cannot overflow
	}
	trips := distance / step
	if distance%step != 0 {
		trips++
	}
	// Check the *last* increment too, rather than merely the compared
	// values: unsigned wrap could otherwise re-enter instead of exiting.
	if trips == 0 || trips > uint64(^uint(0)>>1) || trips > (limit-start)/step {
		return 0
	}
	return int(trips)
}

// exactTripStart admits only a complete, width-matched constant definition.
// movk chains, signed/oversized literals, and entry pseudo-definitions are
// deliberately not part of this small recognizer.
func (f *Function) exactTripStart(instruction *Instr, class asm.RegClass) (uint64, bool) {
	if len(instruction.Asm.Operands) != 2 {
		return 0, false
	}
	destination, ok := instruction.Asm.Operands[0].(asm.Register)
	if !ok || destination.Class != class {
		return 0, false
	}
	value, known := f.t.constant(instruction.Asm)
	if !known || value < 0 {
		return 0, false
	}
	if source, register := instruction.Asm.Operands[1].(asm.Register); register && (instruction.Asm.Mnemonic != "mov" || source.Class != class) {
		return 0, false
	}
	if instruction.Asm.Mnemonic == "movz" && value > 65535 {
		return 0, false
	}
	return uint64(value), true
}

// isTrapBlock reports a block that only traps: the target of the body's
// guards (`b.hs trap`), whose first instruction is the trap.
func isTrapBlock(block *Block) bool {
	return block != nil && len(block.Instrs) > 0 && block.Instrs[0].Trap
}

// loopSuccessors is a block's successors without the trap block.
func loopSuccessors(block *Block) []*Block {
	var out []*Block
	for _, succ := range block.Succs {
		if !isTrapBlock(succ) {
			out = append(out, succ)
		}
	}
	return out
}
