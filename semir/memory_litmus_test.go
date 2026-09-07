package semir

import "testing"

func allPermutations(ids []MemoryEventID, visit func([]MemoryEventID) bool) bool {
	values := append([]MemoryEventID(nil), ids...)
	var walk func(int) bool
	walk = func(index int) bool {
		if index == len(values) {
			order := append([]MemoryEventID(nil), values...)
			return visit(order)
		}
		for i := index; i < len(values); i++ {
			values[index], values[i] = values[i], values[index]
			if walk(index + 1) {
				return true
			}
			values[index], values[i] = values[i], values[index]
		}
		return false
	}
	return walk(0)
}

func hasValidSCWitness(x MemoryExecution, ids []MemoryEventID) bool {
	workspace := memoryWorkspace(len(x.Events))
	return allPermutations(ids, func(order []MemoryEventID) bool {
		return x.ValidateSequentialConsistency(SequentialConsistencyWitness{Order: order}, workspace) == nil
	})
}

// SB: each thread stores then loads the other location. Under seq-cst, the
// outcome r0=0 && r1=0 would require the cycle
// Wx <S Ry <S Wy <S Rx <S Wx, so no global S can witness it.
func TestLitmusStoreBufferingSeqCstBothZeroForbidden(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		// T0: x=1; r0=y(initial)
		{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
		// T1: y=1; r1=x(initial)
		{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("SB execution shape rejected: %v", err)
	}
	if hasValidSCWitness(x, []MemoryEventID{0, 1, 2, 3}) {
		t.Fatal("seq-cst store-buffering both-zero outcome unexpectedly has a global SC witness")
	}
}

// The same SB outcome is allowed by the language for all-relaxed atomics: all
// accesses are atomic so there is no data race, and relaxed creates no SW edge.
func TestLitmusStoreBufferingRelaxedBothZeroAllowed(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderRelaxed},
		{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderRelaxed},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("relaxed SB outcome should be a valid execution: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if a, b, race, err := x.FirstDataRace(workspace); err != nil || race {
		t.Fatalf("all-atomic relaxed SB must remain data-race-free: (%d,%d) race=%v err=%v", a, b, race, err)
	}
}

// MP: a release/acquire flag publishes an ordinary payload. The consumer
// seeing the flag write necessarily orders the payload write before its read.
func TestLitmusMessagePassingReleaseAcquirePublishesPayload(t *testing.T) {
	x := releaseAcquirePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("MP execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 3, workspace); err != nil || !hb {
		t.Fatalf("MP payload publication missing: hb=%v err=%v", hb, err)
	}
}

// IRIW: two SC writers and two SC readers cannot disagree on writer order as
// x=1,y=0 and y=1,x=0. Exhausting 6! candidate S orders provides an executable
// small-state witness check rather than relying on one hand-picked ordering.
func TestLitmusIRIWSeqCstSplitObservationForbidden(t *testing.T) {
	x := MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0}, // Wx
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0}, // Wy
			{Thread: 2, Sequence: 0, Location: 1, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 0},          // Rx=1
			{Thread: 2, Sequence: 1, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},                                     // Ry=0
			{Thread: 3, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 1},          // Ry=1
			{Thread: 3, Sequence: 1, Location: 1, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},                                     // Rx=0
		},
		Synchronizes: []MemorySyncEdge{
			{From: 0, To: 2, Kind: MemorySyncReleaseAcquire},
			{From: 1, To: 4, Kind: MemorySyncReleaseAcquire},
		},
	}
	if err := x.Validate(); err != nil {
		t.Fatalf("IRIW execution shape rejected: %v", err)
	}
	if hasValidSCWitness(x, []MemoryEventID{0, 1, 2, 3, 4, 5}) {
		t.Fatal("seq-cst IRIW split observation unexpectedly has a global SC witness")
	}
}

// LB: loads precede stores in both threads. Both initial reads are compatible
// with a global SC order that places both loads before both stores. This test
// guards against accidentally making Oak seq-cst stronger than its contract.
func TestLitmusLoadBufferingSeqCstBothZeroAllowed(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
		{Thread: 0, Sequence: 1, Location: 1, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 1, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
		{Thread: 1, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("LB execution shape rejected: %v", err)
	}
	if !hasValidSCWitness(x, []MemoryEventID{0, 1, 2, 3}) {
		t.Fatal("seq-cst load-buffering both-zero outcome should have at least one valid global SC witness")
	}
}
