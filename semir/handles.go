package semir

// Generational handles implement docs/spec/60-effects-allocation.md section 7:
// Handle[T] is object identity — slot plus generation — not a pointer synonym
// and not an allocator. The operations are maintained as transliterations of
// spec/lean/Oak/Handles.lean: Resolve is Oak.Handles.Resolves, Free is
// Oak.Handles.clear (occupancy drops, the generation is kept), and slot reuse
// inside Allocate is Oak.Handles.reuse (the generation advances before the
// slot is re-occupied), so every stale handle to the prior occupant stops
// resolving atomically.

// Handle names an object by slot identity and the generation the slot had
// when the object was created. A handle whose generation no longer matches
// its slot is stale and never resolves.
type Handle struct {
	Slot       uint32
	Generation uint32
}

type handleSlot struct {
	generation uint32
	occupied   bool
}

// maxHandleGeneration is the last generation a slot may reach. The Lean model
// uses unbounded naturals; the concrete representation is 32-bit, so a slot
// arriving here is retired instead of wrapping, failing closed against ABA
// aliasing between a stale handle and a reused slot.
const maxHandleGeneration = ^uint32(0)

// maxHandleSlots bounds slot identity to the 32-bit slot index space.
const maxHandleSlots = uint64(^uint32(0)) + 1

// HandleTable owns slot state for one handle domain.
type HandleTable struct {
	slots []handleSlot
	// free holds freed, still-reusable slot indices. Slots whose generation
	// space is exhausted are retired by omission and never reused.
	free []uint32
}

// Allocate occupies a slot and returns its handle. Freed slots are reused
// with an advanced generation (Oak.Handles.reuse); otherwise a fresh slot is
// appended at generation zero. Allocation fails only when slot identity or a
// reused slot's generation space is exhausted.
func (t *HandleTable) Allocate() (Handle, bool) {
	for len(t.free) > 0 {
		index := t.free[len(t.free)-1]
		t.free = t.free[:len(t.free)-1]
		slot := &t.slots[index]
		if slot.generation == maxHandleGeneration {
			// Retire the slot: reusing it would wrap the generation and let a
			// stale handle resolve against a new object.
			continue
		}
		// Oak.Handles.reuse: advance the generation before re-occupancy.
		slot.generation++
		slot.occupied = true
		return Handle{Slot: index, Generation: slot.generation}, true
	}
	if uint64(len(t.slots)) >= maxHandleSlots {
		return Handle{}, false
	}
	t.slots = append(t.slots, handleSlot{generation: 0, occupied: true})
	return Handle{Slot: uint32(len(t.slots) - 1), Generation: 0}, true
}

// Resolve reports whether the handle still names a live object:
// Oak.Handles.Resolves requires occupancy and exact generation equality.
// Unknown slots never resolve.
func (t *HandleTable) Resolve(h Handle) bool {
	if uint64(h.Slot) >= uint64(len(t.slots)) {
		return false
	}
	slot := t.slots[h.Slot]
	return slot.occupied && slot.generation == h.Generation
}

// Free clears the slot named by a currently-resolving handle and queues it
// for generation-advancing reuse. Oak.Handles.clear keeps the generation, so
// the freed handle and all its copies stop resolving immediately. Freeing a
// stale or unknown handle is refused and changes nothing.
func (t *HandleTable) Free(h Handle) bool {
	if !t.Resolve(h) {
		return false
	}
	t.slots[h.Slot].occupied = false
	t.free = append(t.free, h.Slot)
	return true
}

// Live counts currently occupied slots.
func (t *HandleTable) Live() int {
	live := 0
	for _, slot := range t.slots {
		if slot.occupied {
			live++
		}
	}
	return live
}
