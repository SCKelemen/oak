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
	return removed
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
