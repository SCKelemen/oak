package semir

import "testing"

func memoryWorkspace(n int) MemoryWorkspace {
	return MemoryWorkspace{
		Visited: make([]bool, n),
		Stack:   make([]MemoryEventID, n),
	}
}

func releaseAcquirePublication() MemoryExecution {
	// T0: payload=7; release flag=1
	// T1: acquire flag (reads-from release); read payload
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 1},
			{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{From: 1, To: 2, Kind: MemorySyncReleaseAcquire}},
	}
}

func releaseSequencePublication() MemoryExecution {
	// T0 publishes payload through release store M0. Two other threads perform
	// relaxed RMW M1/M2, and the consumer acquire-load observes M2.
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
			{Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessReadWrite, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 1, HasModification: true, Modification: 1},
			{Thread: 3, Sequence: 0, Location: 2, Access: MemoryAccessReadWrite, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 2, HasModification: true, Modification: 2},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 3},
			{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{From: 1, To: 4, Kind: MemorySyncReleaseSequenceAcquire}},
	}
}

func releaseFencePublication() MemoryExecution {
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Access: MemoryAccessFence, Atomic: true, Order: MemoryOrderRelease},
			{Thread: 0, Sequence: 2, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 2},
			{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{
			From: 1, To: 3, Kind: MemorySyncReleaseFenceAcquire,
			HasWriteWitness: true, WriteWitness: 2,
		}},
	}
}

func acquireFencePublication() MemoryExecution {
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 1},
			{Thread: 1, Sequence: 1, Access: MemoryAccessFence, Atomic: true, Order: MemoryOrderAcquire},
			{Thread: 1, Sequence: 2, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{
			From: 1, To: 3, Kind: MemorySyncReleaseAcquireFence,
			HasReadWitness: true, ReadWitness: 2,
		}},
	}
}

func fenceFencePublication() MemoryExecution {
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Access: MemoryAccessFence, Atomic: true, Order: MemoryOrderRelease},
			{Thread: 0, Sequence: 2, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 2},
			{Thread: 1, Sequence: 1, Access: MemoryAccessFence, Atomic: true, Order: MemoryOrderAcquire},
			{Thread: 1, Sequence: 2, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{
			From: 1, To: 4, Kind: MemorySyncReleaseFenceAcquireFence,
			HasWriteWitness: true, WriteWitness: 2,
			HasReadWitness: true, ReadWitness: 3,
		}},
	}
}

func TestReleaseAcquirePublicationCreatesHappensBefore(t *testing.T) {
	x := releaseAcquirePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("valid publication execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))

	if got, err := x.HappensBefore(0, 3, workspace); err != nil || !got {
		t.Fatalf("payload write should happen-before payload read: got=%v err=%v", got, err)
	}
	if race, err := x.IsDataRace(0, 3, workspace); err != nil || race {
		t.Fatalf("published payload should not race: race=%v err=%v", race, err)
	}
}

func TestReleaseSequenceCarriesPublicationAcrossRelaxedRMWs(t *testing.T) {
	x := releaseSequencePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("valid release sequence rejected: %v", err)
	}
	if in, err := x.InReleaseSequence(1, 3); err != nil || !in {
		t.Fatalf("M2 should belong to release sequence headed by M0: in=%v err=%v", in, err)
	}
	if !x.ModificationBefore(1, 2) || !x.ModificationBefore(2, 3) {
		t.Fatal("expected M0 < M1 < M2 in per-location modification order")
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 5, workspace); err != nil || !hb {
		t.Fatalf("release sequence should publish payload: hb=%v err=%v", hb, err)
	}
	if race, err := x.IsDataRace(0, 5, workspace); err != nil || race {
		t.Fatalf("release-sequence-published payload should not race: race=%v err=%v", race, err)
	}
}

func TestNonRMWModificationBreaksReleaseSequence(t *testing.T) {
	x := releaseSequencePublication()
	x.Events[2] = MemoryEvent{
		Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessWrite,
		Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 1,
	}
	// M2 remains a valid RMW immediately after the intervening store, so the
	// execution is structurally valid; only the release-sequence edge is false.
	if err := x.Validate(); err == nil {
		t.Fatal("release-sequence edge unexpectedly crossed a non-RMW modification")
	}
	x.Synchronizes = nil
	if err := x.Validate(); err != nil {
		t.Fatalf("execution without invalid sync edge should remain valid: %v", err)
	}
	if in, err := x.InReleaseSequence(1, 3); err != nil || in {
		t.Fatalf("non-RMW store must break release sequence: in=%v err=%v", in, err)
	}
}

func TestRMWMustReadImmediatelyPreviousModification(t *testing.T) {
	x := releaseSequencePublication()
	x.Events[2].Modification = 2
	if err := x.Validate(); err == nil {
		t.Fatal("RMW that skips a modification index unexpectedly validated")
	}
}

func TestModificationOrderIndicesUniquePerLocation(t *testing.T) {
	x := releaseSequencePublication()
	x.Events[3].Modification = 1
	x.Events[3].ReadsFrom = 1
	if err := x.Validate(); err == nil {
		t.Fatal("duplicate modification index unexpectedly validated")
	}
}

func TestReleaseFencePublishesThroughRelaxedStore(t *testing.T) {
	x := releaseFencePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("valid release-fence publication rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 4, workspace); err != nil || !hb {
		t.Fatalf("release fence should publish payload: hb=%v err=%v", hb, err)
	}
}

func TestAcquireFenceConsumesReleasePublication(t *testing.T) {
	x := acquireFencePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("valid acquire-fence publication rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 4, workspace); err != nil || !hb {
		t.Fatalf("acquire fence should consume publication: hb=%v err=%v", hb, err)
	}
}

func TestReleaseFenceSynchronizesWithAcquireFence(t *testing.T) {
	x := fenceFencePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("valid fence-fence publication rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 5, workspace); err != nil || !hb {
		t.Fatalf("fence-fence chain should publish payload: hb=%v err=%v", hb, err)
	}
}

func TestFenceWitnessMustBeSequencedAroundAtomicPair(t *testing.T) {
	x := fenceFencePublication()
	x.Events[2].Sequence = 0 // write is now before the release fence.
	if err := x.Validate(); err == nil {
		t.Fatal("release fence after write unexpectedly validated as publication")
	}
}

func TestUnsynchronizedConflictingNonAtomicAccessesRace(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 9, Access: MemoryAccessWrite},
		{Thread: 1, Sequence: 0, Location: 9, Access: MemoryAccessRead},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if race, err := x.IsDataRace(0, 1, workspace); err != nil || !race {
		t.Fatalf("unordered conflicting accesses must race: race=%v err=%v", race, err)
	}
	left, right, found, err := x.FirstDataRace(workspace)
	if err != nil || !found || left != 0 || right != 1 {
		t.Fatalf("first race = (%d,%d,%v,%v), want (0,1,true,nil)", left, right, found, err)
	}
}

func TestAtomicAndNonAtomicConflictStillRaces(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 4, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 4, Access: MemoryAccessRead},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if race, err := x.IsDataRace(0, 1, workspace); err != nil || !race {
		t.Fatalf("mixed atomic/non-atomic conflict must race: race=%v err=%v", race, err)
	}
}

func TestRelaxedReadCannotWitnessAcquireSynchronization(t *testing.T) {
	x := releaseAcquirePublication()
	x.Events[2].Order = MemoryOrderRelaxed
	if err := x.Validate(); err == nil {
		t.Fatal("relaxed reader unexpectedly admitted as acquire synchronization")
	}
}

func TestReadsFromMustMatchSynchronizationSource(t *testing.T) {
	x := releaseAcquirePublication()
	x.Events = append(x.Events, MemoryEvent{
		Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true,
		Order: MemoryOrderRelease, HasModification: true, Modification: 1,
	})
	x.Events[2].ReadsFrom = 4
	if err := x.Validate(); err == nil {
		t.Fatal("sync edge with mismatched reads-from witness unexpectedly validated")
	}
}

func TestSameThreadConflictIsOrderedNotRace(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 2, Location: 1, Access: MemoryAccessWrite},
		{Thread: 0, Sequence: 5, Location: 1, Access: MemoryAccessRead},
	}}
	if err := x.Validate(); err != nil {
		t.Fatalf("execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	if hb, err := x.HappensBefore(0, 1, workspace); err != nil || !hb {
		t.Fatalf("same-thread sequence should be HB: hb=%v err=%v", hb, err)
	}
	if race, err := x.IsDataRace(0, 1, workspace); err != nil || race {
		t.Fatalf("same-thread conflict cannot race: race=%v err=%v", race, err)
	}
}

func TestHappensBeforeRequiresCallerWorkspace(t *testing.T) {
	x := releaseAcquirePublication()
	if _, err := x.HappensBefore(0, 3, MemoryWorkspace{}); err != ErrMemoryWorkspaceTooSmall {
		t.Fatalf("small workspace error = %v, want %v", err, ErrMemoryWorkspaceTooSmall)
	}
}

func TestHappensBeforeTraversalAllocatesNothing(t *testing.T) {
	x := releaseAcquirePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("execution rejected: %v", err)
	}
	workspace := memoryWorkspace(len(x.Events))
	allocs := testing.AllocsPerRun(1000, func() {
		hb, err := x.HappensBefore(0, 3, workspace)
		if err != nil || !hb {
			panic("unexpected HB result")
		}
	})
	if allocs != 0 {
		t.Fatalf("HB traversal allocated %.2f objects per run; want zero", allocs)
	}
}

func TestReleaseSequenceWalkAllocatesNothing(t *testing.T) {
	x := releaseSequencePublication()
	if err := x.Validate(); err != nil {
		t.Fatalf("execution rejected: %v", err)
	}
	allocs := testing.AllocsPerRun(1000, func() {
		in, err := x.InReleaseSequence(1, 3)
		if err != nil || !in {
			panic("unexpected release-sequence result")
		}
	})
	if allocs != 0 {
		t.Fatalf("release-sequence walk allocated %.2f objects per run; want zero", allocs)
	}
}

func TestRaceQueryAllocatesNothing(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 7, Access: MemoryAccessWrite},
		{Thread: 1, Sequence: 0, Location: 7, Access: MemoryAccessRead},
	}}
	workspace := memoryWorkspace(len(x.Events))
	allocs := testing.AllocsPerRun(1000, func() {
		race, err := x.IsDataRace(0, 1, workspace)
		if err != nil || !race {
			panic("unexpected race result")
		}
	})
	if allocs != 0 {
		t.Fatalf("race query allocated %.2f objects per run; want zero", allocs)
	}
}
