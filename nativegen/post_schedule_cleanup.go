package nativegen

import "github.com/SCKelemen/oak/asm"

// postScheduleCleanup reruns the established block-local cleanup after the
// scheduler and the final address/forwarding transforms have exposed their
// machine spelling, with the zero-store rule (a zero moved only to be stored
// is the zero register stored) that the early cleanup leaves to it; candidate selection
// remains gated by the seam checker and the unchanged whole-body verifier.
func postScheduleCleanup(fn *asm.Function) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	items, removed := cleanupItemsWith(fn.Items, true)
	if removed != 0 {
		fn.Items = items
	}
	removed += postScheduleRecomputationCleanup(fn)
	return removed
}

// postScheduleRecomputationCleanup removes an exact repeated add-immediate
// when the first computation dominates the second and both its source and
// destination are unchanged on every path between them. This deliberately
// starts with the one final-address shape exposed by allocation and scheduling;
// other arithmetic remains for a general MachineIR value-numbering pass. The
// containing post-schedule candidate is still seam-checked and verdict-gated.
func postScheduleRecomputationCleanup(fn *asm.Function) int {
	removed := 0
	for {
		succ, ok := itemSuccessors(fn.Items)
		if !ok {
			return removed
		}
		changed := false
		for first := 0; first < len(fn.Items) && !changed; first++ {
			firstDest, firstSource, firstImmediate, firstOK := addImmediateComputation(fn.Items[first])
			if !firstOK {
				continue
			}
			for second := first + 1; second < len(fn.Items); second++ {
				secondDest, secondSource, secondImmediate, secondOK := addImmediateComputation(fn.Items[second])
				if !secondOK || secondDest != firstDest || secondSource != firstSource || secondImmediate != firstImmediate ||
					!itemDominates(succ, first, second) ||
					!addImmediateOperandsStable(fn.Items, succ, first+1, second, firstDest.Num, firstSource.Num) {
					continue
				}
				fn.Items = append(fn.Items[:second], fn.Items[second+1:]...)
				removed++
				changed = true
				break
			}
		}
		if !changed {
			return removed
		}
	}
}

func addImmediateComputation(item asm.Item) (dest, source asm.Register, immediate asm.Immediate, ok bool) {
	ins, isInstruction := item.(asm.Instruction)
	if !isInstruction || ins.Mnemonic != "add" || ins.Cond != "" || len(ins.Operands) != 3 {
		return asm.Register{}, asm.Register{}, asm.Immediate{}, false
	}
	dest, destOK := generalReg(ins.Operands[0])
	source, sourceOK := generalReg(ins.Operands[1])
	immediate, immediateOK := ins.Operands[2].(asm.Immediate)
	if !destOK || !sourceOK || !immediateOK || dest.Class != source.Class || dest.Num == source.Num {
		return asm.Register{}, asm.Register{}, asm.Immediate{}, false
	}
	return dest, source, immediate, true
}

func addImmediateOperandsStable(items []asm.Item, succ [][]int, start, target, dest, source int) bool {
	from := reachableItems(succ, start, -1)
	to := reverseReachable(succ, target)
	if target < 0 || target >= len(items) || !from[target] {
		return false
	}
	for i, item := range items {
		if i == target || !from[i] || !to[i] {
			continue
		}
		ins, isInstruction := item.(asm.Instruction)
		if !isInstruction {
			continue
		}
		if ins.Mnemonic == "bl" || ins.Mnemonic == "blr" || writesGeneral(ins, dest) || writesGeneral(ins, source) {
			return false
		}
	}
	return true
}

// postScheduleAliasLabelCleanup removes a branch whose target is any label in
// the adjacent label run. Consecutive labels have one encoded address; an Align
// or instruction ends the run. The fixpoint matters when removing a later
// branch makes a preceding branch adjacent to its target aliases.
func postScheduleAliasLabelCleanup(fn *asm.Function) int {
	if fn == nil || (fn.Arch != "" && fn.Arch != asm.ArchArm64) {
		return 0
	}
	removed := 0
	for {
		out := make([]asm.Item, 0, len(fn.Items))
		round := 0
		for i, item := range fn.Items {
			ins, isInstruction := item.(asm.Instruction)
			if !isInstruction || ins.Mnemonic != "b" {
				out = append(out, item)
				continue
			}
			target := branchTarget(ins)
			drop := false
			for j := i + 1; j < len(fn.Items); j++ {
				label, isLabel := fn.Items[j].(asm.Label)
				if !isLabel {
					break
				}
				if label.Name == target {
					drop = true
					break
				}
			}
			if drop {
				round++
				continue
			}
			out = append(out, item)
		}
		if round == 0 {
			return removed
		}
		fn.Items = out
		removed += round
	}
}

// PostScheduledCleanup reports instructions removed by the verifier-gated
// cleanup pass over the final scheduled spelling.
func PostScheduledCleanup(fn *asm.Function) int { return postScheduledCleanup[fn] }

var postScheduledCleanup = map[*asm.Function]int{}
