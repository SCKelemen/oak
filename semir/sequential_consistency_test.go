package semir

import "testing"

func seqCstPublicationExecution() MemoryExecution {
	return MemoryExecution{
		Events: []MemoryEvent{
			{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
			{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
			{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 1},
			{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
		},
		Synchronizes: []MemorySyncEdge{{From: 1, To: 2, Kind: MemorySyncReleaseAcquire}},
	}
}

func TestSeqCstWitnessAcceptsPublicationOrder(t *testing.T) {
	x := seqCstPublicationExecution()
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1, 2}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err != nil {
		t.Fatalf("valid SC publication rejected: %v", err)
	}
	if !witness.Before(1, 2) || witness.Before(2, 1) {
		t.Fatal("SC witness order lookup is inconsistent")
	}
}

func TestSeqCstWitnessRejectsHappensBeforeReversal(t *testing.T) {
	x := seqCstPublicationExecution()
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{2, 1}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
		t.Fatal("SC order that reverses happens-before unexpectedly validated")
	}
}

func TestSeqCstWitnessRejectsModificationOrderReversal(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 7, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 7, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 1},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1, 0}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
		t.Fatal("SC order that reverses per-location modification order unexpectedly validated")
	}
}

func TestSeqCstReadCannotSkipLaterSCWriteAlreadyBeforeIt(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 1},
		{Thread: 2, Sequence: 0, Location: 5, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 0},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{0, 1, 2}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
		t.Fatal("SC read that skips a later SC-before modification unexpectedly validated")
	}
}

func TestSeqCstReadMayObserveConcurrentNonSCWrite(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 5, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 0},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err != nil {
		t.Fatalf("SC read of concurrent non-SC write rejected: %v", err)
	}
}

func TestSeqCstReadCannotSkipNonSCSourcePastLaterSCWrite(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 1},
		{Thread: 2, Sequence: 0, Location: 5, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst, HasReadsFrom: true, ReadsFrom: 0},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1, 2}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
		t.Fatal("SC read skipped SC-before write after its non-SC source")
	}
}

func TestSeqCstInitialReadRejectsVisibleWrite(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 3, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderSeqCst, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 3, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{0, 1}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
		t.Fatal("SC read of initial value after SC-before write unexpectedly validated")
	}
}

func TestSeqCstInitialReadAllowedWithoutVisibleWrite(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 3, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderSeqCst},
	}}
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{0}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err != nil {
		t.Fatalf("initial SC read with no visible write rejected: %v", err)
	}
}

func TestSeqCstWitnessMustContainEverySCEventExactlyOnce(t *testing.T) {
	x := seqCstPublicationExecution()
	workspace := memoryWorkspace(len(x.Events))
	for name, witness := range map[string]SequentialConsistencyWitness{
		"missing":   {Order: []MemoryEventID{1}},
		"duplicate": {Order: []MemoryEventID{1, 1}},
		"non-sc":    {Order: []MemoryEventID{1, 3}},
	} {
		t.Run(name, func(t *testing.T) {
			if err := x.ValidateSequentialConsistency(witness, workspace); err == nil {
				t.Fatalf("invalid %s SC witness unexpectedly validated", name)
			}
		})
	}
}

func TestSeqCstValidationRequiresCallerWorkspace(t *testing.T) {
	x := seqCstPublicationExecution()
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1, 2}}
	if err := x.ValidateSequentialConsistency(witness, MemoryWorkspace{}); err != ErrMemoryWorkspaceTooSmall {
		t.Fatalf("SC workspace error = %v, want %v", err, ErrMemoryWorkspaceTooSmall)
	}
}

func TestSeqCstValidationAllocatesNothing(t *testing.T) {
	x := seqCstPublicationExecution()
	workspace := memoryWorkspace(len(x.Events))
	witness := SequentialConsistencyWitness{Order: []MemoryEventID{1, 2}}
	if err := x.ValidateSequentialConsistency(witness, workspace); err != nil {
		t.Fatalf("execution rejected before allocation test: %v", err)
	}
	allocs := testing.AllocsPerRun(1000, func() {
		if err := x.ValidateSequentialConsistency(witness, workspace); err != nil {
			panic("unexpected SC validation failure")
		}
	})
	if allocs != 0 {
		t.Fatalf("SC validation allocated %.2f objects per run; want zero", allocs)
	}
}
