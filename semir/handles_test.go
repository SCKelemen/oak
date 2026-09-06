package semir

import "testing"

// Mirrors Oak.Handles.stale_handle_cannot_resolve_after_reuse: once a slot is
// reused, every handle minted for the prior occupant is stale.
func TestStaleHandleCannotResolveAfterReuse(t *testing.T) {
	table := &HandleTable{}
	first, ok := table.Allocate()
	if !ok || !table.Resolve(first) {
		t.Fatalf("fresh handle must resolve: %#v ok=%v", first, ok)
	}
	if !table.Free(first) {
		t.Fatal("freeing a live handle must succeed")
	}
	second, ok := table.Allocate()
	if !ok {
		t.Fatal("reusing a freed slot must succeed")
	}
	if second.Slot != first.Slot {
		t.Fatalf("expected slot reuse, got slot %d then %d", first.Slot, second.Slot)
	}
	if second.Generation != first.Generation+1 {
		t.Fatalf("reuse must advance the generation: %d then %d", first.Generation, second.Generation)
	}
	if table.Resolve(first) {
		t.Fatal("stale handle resolved after generation-advancing reuse")
	}
	if !table.Resolve(second) {
		t.Fatal("current handle must resolve after reuse")
	}
}

// Mirrors Oak.Handles.cleared_slot_never_resolves: freeing clears occupancy,
// so the handle (and any copy of it) stops resolving, and double free is
// refused.
func TestFreedHandleNeverResolves(t *testing.T) {
	table := &HandleTable{}
	h, _ := table.Allocate()
	copyOfH := h
	if !table.Free(h) {
		t.Fatal("freeing a live handle must succeed")
	}
	if table.Resolve(h) || table.Resolve(copyOfH) {
		t.Fatal("freed handle resolved")
	}
	if table.Free(h) {
		t.Fatal("double free must be refused")
	}
	if table.Live() != 0 {
		t.Fatalf("live count = %d after freeing the only handle", table.Live())
	}
}

func TestDistinctSlotsAreIndependent(t *testing.T) {
	table := &HandleTable{}
	a, _ := table.Allocate()
	b, _ := table.Allocate()
	if a.Slot == b.Slot {
		t.Fatalf("distinct live objects must not share a slot: %d", a.Slot)
	}
	if !table.Free(a) {
		t.Fatal("freeing a must succeed")
	}
	if !table.Resolve(b) {
		t.Fatal("freeing one handle must not disturb another slot")
	}
	if table.Live() != 1 {
		t.Fatalf("live count = %d, want 1", table.Live())
	}
}

func TestUnknownSlotNeverResolves(t *testing.T) {
	table := &HandleTable{}
	if table.Resolve(Handle{Slot: 7, Generation: 0}) {
		t.Fatal("handle into an unknown slot resolved")
	}
	if table.Free(Handle{Slot: 7, Generation: 0}) {
		t.Fatal("freeing a handle into an unknown slot must be refused")
	}
}

// The Lean model's generations are unbounded naturals; the 32-bit concrete
// representation fails closed instead: a slot that has exhausted its
// generation space is retired, never reused, so no stale handle can collide
// with a wrapped generation.
func TestGenerationExhaustionRetiresSlot(t *testing.T) {
	table := &HandleTable{
		slots: []handleSlot{{generation: maxHandleGeneration, occupied: false}},
		free:  []uint32{0},
	}
	h, ok := table.Allocate()
	if !ok {
		t.Fatal("allocation must fall through to a fresh slot")
	}
	if h.Slot == 0 {
		t.Fatal("generation-exhausted slot was reused")
	}
	if table.Resolve(Handle{Slot: 0, Generation: maxHandleGeneration}) {
		t.Fatal("retired slot resolved")
	}
	if len(table.free) != 0 {
		t.Fatal("retired slot must leave the free list permanently")
	}
}
