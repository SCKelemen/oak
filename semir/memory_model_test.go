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
			{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 1},
			{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{From: 1, To: 2, Kind: MemorySyncReleaseAcquire}},
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
		{Thread: 0, Sequence: 0, Location: 4, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed},
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
		Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease,
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
