package semir

import "testing"

// The ring protocols of stdlib/rings.oak as executions of the language's
// memory model (docs/spec/67-memory-ordering.md section 9; the Lean
// statements are Oak.Rings.spsc_payload_race_free, spsc_reuse_race_free,
// mpsc_payload_race_free, intrusive_payload_race_free). Each execution is
// one handoff exactly as the ring spells it — the atomic operations, their
// orders, and the reads-from edges a consumer's observation establishes —
// and the validators decide happens-before and races. The negative
// variants show the checks are not vacuous: relaxed publication races, and
// a payload written after its release store is not published.
//
// Locations: 1 the slot's payload, 2 the tail counter, 3 the head counter,
// 4 a slot's sequence cell, 5 a node's link.

func ringHB(t *testing.T, name string, x MemoryExecution, from, to MemoryEventID) {
	t.Helper()
	if err := x.Validate(); err != nil {
		t.Fatalf("%s: execution rejected: %v", name, err)
	}
	ws := memoryWorkspace(len(x.Events))
	hb, err := x.HappensBefore(from, to, ws)
	if err != nil || !hb {
		t.Fatalf("%s: %d does not happen-before %d (err %v)", name, from, to, err)
	}
	if a, b, race, err := x.FirstDataRace(ws); err != nil || race {
		t.Fatalf("%s: unexpected data race (%d, %d), err %v", name, a, b, err)
	}
}

func ringRaces(t *testing.T, name string, x MemoryExecution, a, b MemoryEventID) {
	t.Helper()
	if err := x.Validate(); err != nil {
		t.Fatalf("%s: execution rejected: %v", name, err)
	}
	ws := memoryWorkspace(len(x.Events))
	if hb, _ := x.HappensBefore(a, b, ws); hb {
		t.Fatalf("%s: %d unexpectedly happens-before %d", name, a, b)
	}
	race, err := x.IsDataRace(a, b, ws)
	if err != nil || !race {
		t.Fatalf("%s: expected a data race between %d and %d, got race=%v err=%v", name, a, b, race, err)
	}
}

// SPSC push then pop: the producer writes the slot and releases `tail`; the
// consumer acquires `tail`, reading that store, and reads the slot.
func spscHandoff(store, load MemoryOrder) MemoryExecution {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
		{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: store, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: load, HasReadsFrom: true, ReadsFrom: 1},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
	}}
	if releaseLike(store) && acquireLike(load) {
		x.Synchronizes = []MemorySyncEdge{{From: 1, To: 2, Kind: MemorySyncReleaseAcquire}}
	}
	return x
}

func TestRingLitmusSpscHandoff(t *testing.T) {
	ringHB(t, "spsc handoff (release/acquire)", spscHandoff(MemoryOrderRelease, MemoryOrderAcquire), 0, 3)
	// The consumer's acquire and the producer's release are what the ring
	// spells; relaxed on either side leaves the slot accesses racing.
	ringRaces(t, "spsc handoff (relaxed)", spscHandoff(MemoryOrderRelaxed, MemoryOrderRelaxed), 0, 3)
	ringRaces(t, "spsc handoff (relaxed load)", spscHandoff(MemoryOrderRelease, MemoryOrderRelaxed), 0, 3)
}

// SPSC reuse: the consumer reads the slot and releases `head`; the producer
// acquires `head`, reading that store, and overwrites the slot.
func TestRingLitmusSpscReuse(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 1, Sequence: 0, Location: 1, Access: MemoryAccessRead},
		{Thread: 1, Sequence: 1, Location: 3, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 0, Location: 3, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 1},
		{Thread: 0, Sequence: 1, Location: 1, Access: MemoryAccessWrite},
	}, Synchronizes: []MemorySyncEdge{{From: 1, To: 2, Kind: MemorySyncReleaseAcquire}}}
	ringHB(t, "spsc reuse", x, 0, 3)
}

// A payload written after its release store is not published: the acquire
// observes the store, but nothing orders the later write before the read.
func TestRingLitmusLatePayloadIsNotPublished(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 0, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 1, Location: 1, Access: MemoryAccessWrite},
		{Thread: 1, Sequence: 0, Location: 2, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 0},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
	}, Synchronizes: []MemorySyncEdge{{From: 0, To: 2, Kind: MemorySyncReleaseAcquire}}}
	ringRaces(t, "late payload", x, 1, 3)
}

// MPSC push then pop: thread 2 initializes `tail`; two producers claim
// positions with relaxed compare-exchanges (a modification chain), the
// first writes its slot and releases the slot's sequence cell; the consumer
// acquires the sequence, reading that store, and reads the slot.
func TestRingLitmusMpscHandoff(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 0, Location: 2, Access: MemoryAccessReadWrite, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 0, HasModification: true, Modification: 1},
		{Thread: 3, Sequence: 0, Location: 2, Access: MemoryAccessReadWrite, Atomic: true, Order: MemoryOrderRelaxed, HasReadsFrom: true, ReadsFrom: 1, HasModification: true, Modification: 2},
		{Thread: 0, Sequence: 1, Location: 1, Access: MemoryAccessWrite},
		{Thread: 0, Sequence: 2, Location: 4, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 4, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 4},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
	}, Synchronizes: []MemorySyncEdge{{From: 4, To: 5, Kind: MemorySyncReleaseAcquire}}}
	ringHB(t, "mpsc handoff", x, 3, 6)
	// The claim alone publishes nothing: without the sequence cell's
	// release/acquire the slot accesses race.
	relaxed := x
	relaxed.Events = append([]MemoryEvent(nil), x.Events...)
	relaxed.Events[4].Order, relaxed.Events[5].Order = MemoryOrderRelaxed, MemoryOrderRelaxed
	relaxed.Synchronizes = nil
	ringRaces(t, "mpsc handoff (relaxed sequence)", relaxed, 3, 6)
}

// The intrusive MPSC: the producer writes its node's payload, exchanges
// `head` (acq_rel, a modification after the stub's initial link), and
// releases the previous node's link; the consumer acquires the link,
// reading that store, and reads the payload.
func TestRingLitmusIntrusiveHandoff(t *testing.T) {
	x := MemoryExecution{Events: []MemoryEvent{
		{Thread: 2, Sequence: 0, Location: 2, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelaxed, HasModification: true, Modification: 0},
		{Thread: 0, Sequence: 0, Location: 1, Access: MemoryAccessWrite},
		{Thread: 0, Sequence: 1, Location: 2, Access: MemoryAccessReadWrite, Atomic: true, Order: MemoryOrderAcqRel, HasReadsFrom: true, ReadsFrom: 0, HasModification: true, Modification: 1},
		{Thread: 0, Sequence: 2, Location: 5, Access: MemoryAccessWrite, Atomic: true, Order: MemoryOrderRelease, HasModification: true, Modification: 0},
		{Thread: 1, Sequence: 0, Location: 5, Access: MemoryAccessRead, Atomic: true, Order: MemoryOrderAcquire, HasReadsFrom: true, ReadsFrom: 3},
		{Thread: 1, Sequence: 1, Location: 1, Access: MemoryAccessRead},
	}, Synchronizes: []MemorySyncEdge{{From: 3, To: 4, Kind: MemorySyncReleaseAcquire}}}
	ringHB(t, "intrusive handoff", x, 1, 5)
}

// Under seq_cst the SPSC handoff has a global order — program order of the
// two threads with the acquire after the release — so the outcome the ring
// relies on is witnessed, not merely allowed.
func TestRingLitmusSpscSeqCstWitness(t *testing.T) {
	x := spscHandoff(MemoryOrderSeqCst, MemoryOrderSeqCst)
	if err := x.Validate(); err != nil {
		t.Fatal(err)
	}
	if !hasValidSCWitness(x, []MemoryEventID{1, 2}) {
		t.Fatal("the seq_cst handoff has no sequentially consistent witness")
	}
}
