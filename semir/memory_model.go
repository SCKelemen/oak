package semir

import (
	"errors"
	"fmt"
)

// MemoryEventID is an O(1) index into MemoryExecution.Events.
type MemoryEventID uint32

// MemoryThreadID identifies one execution thread in a memory-model witness.
type MemoryThreadID uint32

// MemoryLocationID is semantic storage identity, not a machine address.
type MemoryLocationID uint64

// MemoryAccessKind classifies the observable memory action of an event.
type MemoryAccessKind uint8

const (
	MemoryAccessNone MemoryAccessKind = iota
	MemoryAccessRead
	MemoryAccessWrite
	MemoryAccessReadWrite
	MemoryAccessFence
)

func (k MemoryAccessKind) reads() bool {
	return k == MemoryAccessRead || k == MemoryAccessReadWrite
}

func (k MemoryAccessKind) writes() bool {
	return k == MemoryAccessWrite || k == MemoryAccessReadWrite
}

// MemoryEvent is one event in an abstract execution witness. Event identity is
// its slice index; this keeps graph traversal compact and deterministic.
//
// Atomic writes and RMWs carry a per-location Modification index. RMWs after
// modification zero must read-from the immediately preceding modification;
// that explicit causal chain is also the witness used for release sequences.
type MemoryEvent struct {
	Thread          MemoryThreadID
	Sequence        uint32
	Location        MemoryLocationID
	Access          MemoryAccessKind
	Atomic          bool
	Order           MemoryOrder
	HasReadsFrom    bool
	ReadsFrom       MemoryEventID
	HasModification bool
	Modification    uint32
}

// MemorySyncKind identifies why an inter-thread synchronizes-with edge exists.
// Each rule is explicit so debuggers/proof projections retain causal provenance
// instead of collapsing every synchronization into an unexplained graph edge.
type MemorySyncKind uint8

const (
	MemorySyncInvalid MemorySyncKind = iota
	MemorySyncReleaseAcquire
	MemorySyncReleaseSequenceAcquire
	MemorySyncReleaseFenceAcquire
	MemorySyncReleaseAcquireFence
	MemorySyncReleaseFenceAcquireFence
)

// MemorySyncEdge is a validated synchronizes-with edge. Fence-mediated rules
// use explicit witness event IDs. Flags are required because event zero is a
// valid witness and must not be overloaded as "missing".
type MemorySyncEdge struct {
	From MemoryEventID
	To   MemoryEventID
	Kind MemorySyncKind

	HasWriteWitness bool
	WriteWitness    MemoryEventID
	HasReadWitness  bool
	ReadWitness     MemoryEventID
}

// MemoryExecution is an explicit execution graph. Slices are supplied by the
// caller; the model does not allocate storage internally.
type MemoryExecution struct {
	Events       []MemoryEvent
	Synchronizes []MemorySyncEdge
}

// MemoryWorkspace is caller-owned traversal scratch. Reusing it keeps HB/race
// analysis allocation-free after setup.
type MemoryWorkspace struct {
	Visited []bool
	Stack   []MemoryEventID
}

var (
	ErrMemoryEventOutOfRange   = errors.New("memory event id out of range")
	ErrMemoryWorkspaceTooSmall = errors.New("memory workspace too small")
)

func releaseLike(order MemoryOrder) bool {
	return order == MemoryOrderRelease || order == MemoryOrderAcqRel || order == MemoryOrderSeqCst
}

func acquireLike(order MemoryOrder) bool {
	return order == MemoryOrderAcquire || order == MemoryOrderAcqRel || order == MemoryOrderSeqCst
}

func legalEventOrder(event MemoryEvent) bool {
	if !event.Atomic {
		return event.Order == ""
	}
	switch event.Access {
	case MemoryAccessRead:
		return LegalAtomicOrder(AtomicLoad, event.Order)
	case MemoryAccessWrite:
		return LegalAtomicOrder(AtomicStore, event.Order)
	case MemoryAccessReadWrite:
		return LegalAtomicOrder(AtomicRMW, event.Order)
	case MemoryAccessFence:
		return LegalAtomicOrder(AtomicFence, event.Order)
	default:
		return false
	}
}

func (x MemoryExecution) event(id MemoryEventID) (MemoryEvent, bool) {
	if int(id) >= len(x.Events) {
		return MemoryEvent{}, false
	}
	return x.Events[id], true
}

func (x MemoryExecution) readsFrom(write, read MemoryEventID) bool {
	w, wok := x.event(write)
	r, rok := x.event(read)
	return wok && rok && w.Atomic && w.Access.writes() && r.Atomic && r.Access.reads() &&
		w.Location == r.Location && r.HasReadsFrom && r.ReadsFrom == write
}

func (x MemoryExecution) isReleaseFence(id MemoryEventID) bool {
	e, ok := x.event(id)
	return ok && e.Atomic && e.Access == MemoryAccessFence && releaseLike(e.Order)
}

func (x MemoryExecution) isAcquireFence(id MemoryEventID) bool {
	e, ok := x.event(id)
	return ok && e.Atomic && e.Access == MemoryAccessFence && acquireLike(e.Order)
}

// InReleaseSequence reports whether member belongs to the release sequence
// headed by head. A sequence is the head itself followed by zero or more
// contiguous RMW modifications. Every RMW member explicitly reads-from the
// immediately preceding modification. The walk is bounded by len(Events) and
// allocates no storage.
func (x MemoryExecution) InReleaseSequence(head, member MemoryEventID) (bool, error) {
	h, ok := x.event(head)
	if !ok {
		return false, ErrMemoryEventOutOfRange
	}
	m, ok := x.event(member)
	if !ok {
		return false, ErrMemoryEventOutOfRange
	}
	if !h.Atomic || !h.Access.writes() || !releaseLike(h.Order) || !h.HasModification ||
		!m.Atomic || !m.Access.writes() || !m.HasModification || h.Location != m.Location ||
		m.Modification < h.Modification {
		return false, nil
	}
	if head == member {
		return true, nil
	}

	current := member
	for steps := 0; steps < len(x.Events); steps++ {
		if current == head {
			return true, nil
		}
		e := x.Events[current]
		if e.Access != MemoryAccessReadWrite || !e.HasReadsFrom || e.Modification == 0 {
			return false, nil
		}
		previous := e.ReadsFrom
		p, ok := x.event(previous)
		if !ok || !p.Atomic || !p.Access.writes() || !p.HasModification ||
			p.Location != h.Location || p.Modification == ^uint32(0) ||
			p.Modification+1 != e.Modification {
			return false, nil
		}
		current = previous
	}
	// More links than events implies a malformed cycle/repeated witness.
	return false, nil
}

func (edge MemorySyncEdge) noWitnesses() bool {
	return !edge.HasWriteWitness && !edge.HasReadWitness
}

// Validate checks the structural execution witness. It is deliberately
// separate from graph queries so hot verification/model-checking loops can
// validate once and reuse allocation-free reachability operations many times.
func (x MemoryExecution) Validate() error {
	for i, event := range x.Events {
		if !legalEventOrder(event) {
			return fmt.Errorf("event %d has illegal atomic/non-atomic order", i)
		}

		if event.Access == MemoryAccessFence {
			if !event.Atomic || event.HasReadsFrom || event.HasModification {
				return fmt.Errorf("event %d has invalid fence shape", i)
			}
		} else if event.Access == MemoryAccessNone {
			return fmt.Errorf("event %d has no memory access", i)
		}

		if event.Atomic && event.Access.writes() {
			if !event.HasModification {
				return fmt.Errorf("atomic write event %d lacks modification-order index", i)
			}
		} else if event.HasModification {
			return fmt.Errorf("non-writing event %d carries modification-order index", i)
		}

		if event.HasReadsFrom {
			if !event.Atomic || !event.Access.reads() {
				return fmt.Errorf("event %d has reads-from but is not an atomic read", i)
			}
			if int(event.ReadsFrom) >= len(x.Events) {
				return fmt.Errorf("event %d reads-from out-of-range event %d", i, event.ReadsFrom)
			}
			source := x.Events[event.ReadsFrom]
			if !source.Atomic || !source.Access.writes() || source.Location != event.Location {
				return fmt.Errorf("event %d has invalid reads-from source %d", i, event.ReadsFrom)
			}
		}

		// An RMW observes and replaces the immediately preceding modification.
		// Modification zero may observe the implicit initial value and therefore
		// has no represented reads-from source.
		if event.Atomic && event.Access == MemoryAccessReadWrite {
			if event.Modification == 0 {
				if event.HasReadsFrom {
					return fmt.Errorf("initial RMW event %d cannot read-from a represented modification", i)
				}
			} else {
				if !event.HasReadsFrom {
					return fmt.Errorf("RMW event %d lacks previous-modification reads-from witness", i)
				}
				source := x.Events[event.ReadsFrom]
				if !source.HasModification || source.Modification == ^uint32(0) ||
					source.Modification+1 != event.Modification {
					return fmt.Errorf("RMW event %d does not read the immediately preceding modification", i)
				}
			}
		}
	}

	// Sequence numbers define per-thread source order and must be unique.
	// Modification indices define a total order among represented atomic writes
	// on one location and must likewise be unique.
	for i := 0; i < len(x.Events); i++ {
		for j := i + 1; j < len(x.Events); j++ {
			if x.Events[i].Thread == x.Events[j].Thread && x.Events[i].Sequence == x.Events[j].Sequence {
				return fmt.Errorf("events %d and %d duplicate thread sequence", i, j)
			}
			if x.Events[i].HasModification && x.Events[j].HasModification &&
				x.Events[i].Location == x.Events[j].Location &&
				x.Events[i].Modification == x.Events[j].Modification {
				return fmt.Errorf("events %d and %d duplicate modification index", i, j)
			}
		}
	}

	for i, edge := range x.Synchronizes {
		if int(edge.From) >= len(x.Events) || int(edge.To) >= len(x.Events) {
			return fmt.Errorf("sync edge %d references an out-of-range event", i)
		}
		if edge.From == edge.To {
			return fmt.Errorf("sync edge %d is self-referential", i)
		}

		from := x.Events[edge.From]
		to := x.Events[edge.To]
		switch edge.Kind {
		case MemorySyncReleaseAcquire:
			if !edge.noWitnesses() {
				return fmt.Errorf("direct sync edge %d has unexpected witnesses", i)
			}
			if !from.Atomic || !from.Access.writes() || !releaseLike(from.Order) {
				return fmt.Errorf("sync edge %d source is not a release-like atomic write", i)
			}
			if !to.Atomic || !to.Access.reads() || !acquireLike(to.Order) {
				return fmt.Errorf("sync edge %d target is not an acquire-like atomic read", i)
			}
			if !x.readsFrom(edge.From, edge.To) {
				return fmt.Errorf("sync edge %d is not witnessed by reads-from on one location", i)
			}

		case MemorySyncReleaseSequenceAcquire:
			if !edge.noWitnesses() || !to.Atomic || !to.Access.reads() || !acquireLike(to.Order) || !to.HasReadsFrom {
				return fmt.Errorf("release-sequence sync edge %d has invalid target/witness shape", i)
			}
			member := to.ReadsFrom
			inSequence, err := x.InReleaseSequence(edge.From, member)
			if err != nil || !inSequence {
				return fmt.Errorf("release-sequence sync edge %d is not witnessed by a valid release sequence", i)
			}

		case MemorySyncReleaseFenceAcquire:
			if !x.isReleaseFence(edge.From) || !to.Atomic || !to.Access.reads() || !acquireLike(to.Order) ||
				!edge.HasWriteWitness || edge.HasReadWitness {
				return fmt.Errorf("release-fence sync edge %d has invalid shape", i)
			}
			write, ok := x.event(edge.WriteWitness)
			if !ok || !write.Atomic || !write.Access.writes() ||
				!x.SequencedBefore(edge.From, edge.WriteWitness) || !x.readsFrom(edge.WriteWitness, edge.To) {
				return fmt.Errorf("release-fence sync edge %d lacks write/read-from witness", i)
			}

		case MemorySyncReleaseAcquireFence:
			if !from.Atomic || !from.Access.writes() || !releaseLike(from.Order) ||
				!x.isAcquireFence(edge.To) || edge.HasWriteWitness || !edge.HasReadWitness {
				return fmt.Errorf("acquire-fence sync edge %d has invalid shape", i)
			}
			read, ok := x.event(edge.ReadWitness)
			if !ok || !read.Atomic || !read.Access.reads() || !read.HasReadsFrom ||
				!x.SequencedBefore(edge.ReadWitness, edge.To) {
				return fmt.Errorf("acquire-fence sync edge %d lacks preceding atomic read", i)
			}
			member := read.ReadsFrom
			if member == edge.From {
				if !x.readsFrom(edge.From, edge.ReadWitness) {
					return fmt.Errorf("acquire-fence sync edge %d has invalid direct reads-from", i)
				}
			} else {
				inSequence, err := x.InReleaseSequence(edge.From, member)
				if err != nil || !inSequence {
					return fmt.Errorf("acquire-fence sync edge %d lacks release-sequence witness", i)
				}
			}

		case MemorySyncReleaseFenceAcquireFence:
			if !x.isReleaseFence(edge.From) || !x.isAcquireFence(edge.To) ||
				!edge.HasWriteWitness || !edge.HasReadWitness {
				return fmt.Errorf("fence-fence sync edge %d has invalid shape", i)
			}
			write, wok := x.event(edge.WriteWitness)
			read, rok := x.event(edge.ReadWitness)
			if !wok || !rok || !write.Atomic || !write.Access.writes() ||
				!read.Atomic || !read.Access.reads() ||
				!x.SequencedBefore(edge.From, edge.WriteWitness) ||
				!x.SequencedBefore(edge.ReadWitness, edge.To) ||
				!x.readsFrom(edge.WriteWitness, edge.ReadWitness) {
				return fmt.Errorf("fence-fence sync edge %d lacks write/read witnesses", i)
			}

		default:
			return fmt.Errorf("sync edge %d has unknown kind", i)
		}
	}
	return nil
}

// SequencedBefore is per-thread source/execution order.
func (x MemoryExecution) SequencedBefore(from, to MemoryEventID) bool {
	if int(from) >= len(x.Events) || int(to) >= len(x.Events) || from == to {
		return false
	}
	a := x.Events[from]
	b := x.Events[to]
	return a.Thread == b.Thread && a.Sequence < b.Sequence
}

// ModificationBefore is the represented per-location atomic modification order.
func (x MemoryExecution) ModificationBefore(from, to MemoryEventID) bool {
	if int(from) >= len(x.Events) || int(to) >= len(x.Events) || from == to {
		return false
	}
	a := x.Events[from]
	b := x.Events[to]
	return a.HasModification && b.HasModification && a.Location == b.Location &&
		a.Modification < b.Modification
}

// SynchronizesWith checks validated explicit inter-thread synchronization.
func (x MemoryExecution) SynchronizesWith(from, to MemoryEventID) bool {
	for i := range x.Synchronizes {
		edge := x.Synchronizes[i]
		if edge.From == from && edge.To == to {
			return true
		}
	}
	return false
}

func (x MemoryExecution) baseBefore(from, to MemoryEventID) bool {
	return x.SequencedBefore(from, to) || x.SynchronizesWith(from, to)
}

// HappensBefore is the transitive closure of sequenced-before union
// synchronizes-with. It performs no internal allocation: callers provide one
// visited bit per event and one stack slot per event.
func (x MemoryExecution) HappensBefore(from, to MemoryEventID, workspace MemoryWorkspace) (bool, error) {
	if int(from) >= len(x.Events) || int(to) >= len(x.Events) {
		return false, ErrMemoryEventOutOfRange
	}
	if len(workspace.Visited) < len(x.Events) || len(workspace.Stack) < len(x.Events) {
		return false, ErrMemoryWorkspaceTooSmall
	}
	if from == to {
		return false, nil
	}
	for i := 0; i < len(x.Events); i++ {
		workspace.Visited[i] = false
	}

	top := 0
	workspace.Stack[top] = from
	top++
	workspace.Visited[from] = true

	for top > 0 {
		top--
		current := workspace.Stack[top]
		for next := 0; next < len(x.Events); next++ {
			nextID := MemoryEventID(next)
			if workspace.Visited[next] || !x.baseBefore(current, nextID) {
				continue
			}
			if nextID == to {
				return true, nil
			}
			workspace.Visited[next] = true
			workspace.Stack[top] = nextID
			top++
		}
	}
	return false, nil
}

// Conflicts is the language-level conflicting-access predicate.
func (x MemoryExecution) Conflicts(a, b MemoryEventID) bool {
	if int(a) >= len(x.Events) || int(b) >= len(x.Events) || a == b {
		return false
	}
	left := x.Events[a]
	right := x.Events[b]
	if left.Access == MemoryAccessFence || right.Access == MemoryAccessFence || left.Location != right.Location {
		return false
	}
	return left.Access.writes() || right.Access.writes()
}

// IsDataRace follows Oak's fail-closed race definition: different threads,
// conflicting accesses, at least one non-atomic access, and no HB edge in
// either direction. Mixing atomic and non-atomic access does not escape the
// race rule.
func (x MemoryExecution) IsDataRace(a, b MemoryEventID, workspace MemoryWorkspace) (bool, error) {
	if int(a) >= len(x.Events) || int(b) >= len(x.Events) {
		return false, ErrMemoryEventOutOfRange
	}
	left := x.Events[a]
	right := x.Events[b]
	if left.Thread == right.Thread || !x.Conflicts(a, b) || (left.Atomic && right.Atomic) {
		return false, nil
	}
	ab, err := x.HappensBefore(a, b, workspace)
	if err != nil || ab {
		return false, err
	}
	ba, err := x.HappensBefore(b, a, workspace)
	if err != nil || ba {
		return false, err
	}
	return true, nil
}

// FirstDataRace deterministically returns the lexicographically first event
// pair that races. It reuses caller scratch and allocates no storage itself.
func (x MemoryExecution) FirstDataRace(workspace MemoryWorkspace) (MemoryEventID, MemoryEventID, bool, error) {
	for i := 0; i < len(x.Events); i++ {
		for j := i + 1; j < len(x.Events); j++ {
			race, err := x.IsDataRace(MemoryEventID(i), MemoryEventID(j), workspace)
			if err != nil {
				return 0, 0, false, err
			}
			if race {
				return MemoryEventID(i), MemoryEventID(j), true, nil
			}
		}
	}
	return 0, 0, false, nil
}
