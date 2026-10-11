package nativegen

import (
	"weak"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
)

// loweringMetadata belongs to one lowered function. Keeping it on that
// function allows rejected candidates and all their assembly context to be
// collected instead of rooting them in package-global pointer-keyed maps.
//
// The weak identity preserves the old maps' copy boundary: machine passes
// and OptIR selectors shallow-copy asm.Function, but their new outputs did
// not inherit nativegen metadata. In particular, an OptIR template's frame
// objects do not describe the selector's new frame. A strong owner pointer
// would keep templates alive through copies and create finalizer cycles.
// None of this bookkeeping is a verdict or checked-source authority.
type loweringMetadata struct {
	owner                      weak.Pointer[asm.Function]
	carriedLoopIndices         int
	cleanedCopies              int
	sharedGlobalAddresses      int
	forwardedGlobalLoads       int
	elidedGlobalLoadMasks      int
	loopArrayHomesOf           int
	loopResultHomesOf          int
	fusedMultiplies            int
	scheduledOf                int
	fusedOf                    int
	fusedExitsOf               int
	evictedLeafCalleeSaves     int
	retainedCalleeSaveCarriers int
	trimmedCalleeSaves         int
	elidedEmptyFrames          int
	optIRLowered               int
	frameObjectsOf             []machine.FrameObject
	reallocated                int
	promotedSlots              int
	elidedGuards               int
	reusedCompares             int
	hoistedLoops               int
	rotatedLoops               int
	reducedOps                 int
	vectorHomesOf              int
	leafVectorHomesOf          int
	rotatedOps                 int
	// pressured asks the direct ARM64 lowering to retry with spare scratch homes.
	pressured                             bool
	postScheduledCleanup                  int
	sharedRecordBases                     int
	reusedRecordBaseDestinations          int
	reusedRemainingRecordBaseDestinations int
	rescheduledRecordBaseCarriers         int
	redundantGuards                       int
	rewriteSitesOf                        []RewriteSite
	valueSelects                          int
	fusedVectorBlocks                     int
	sharedVectorAddressCount              int
}

// emptyLoweringMetadata is read-only. Reading absent or copied metadata must
// neither allocate nor mutate a function, including concurrent readers.
var emptyLoweringMetadata loweringMetadata

func readLoweringMetadata(fn *asm.Function) *loweringMetadata {
	if fn != nil {
		if metadata, ok := fn.LoweringMetadata.(*loweringMetadata); ok && metadata != nil && metadata.owner.Value() == fn {
			return metadata
		}
	}
	return &emptyLoweringMetadata
}

// editLoweringMetadata is used only while lowering a function. Each candidate
// gets its own mutable record, even if its assembly started as a shallow copy.
// Like its Items and Frame, metadata for one function is not concurrently
// mutable; independently lowered functions share no mutable bookkeeping.
func editLoweringMetadata(fn *asm.Function) *loweringMetadata {
	if metadata := readLoweringMetadata(fn); metadata != &emptyLoweringMetadata {
		return metadata
	}
	metadata := &loweringMetadata{owner: weak.Make(fn)}
	fn.LoweringMetadata = metadata
	return metadata
}
