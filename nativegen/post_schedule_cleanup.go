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

// PostScheduledCleanup reports instructions removed by the verifier-gated
// cleanup pass over the final scheduled spelling.
func PostScheduledCleanup(fn *asm.Function) int { return postScheduledCleanup[fn] }

var postScheduledCleanup = map[*asm.Function]int{}
