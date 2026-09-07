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
type MemoryEvent struct {
	Thread       MemoryThreadID
	Sequence     uint32
	Location     MemoryLocationID
	Access       MemoryAccessKind
	Atomic       bool
	Order        MemoryOrder
	HasReadsFrom bool
	ReadsFrom    MemoryEventID
}

// MemorySyncKind identifies why an inter-thread synchronizes-with edge exists.
// The first executable slice admits direct release/acquire publication edges.
// Fence/release-sequence witnesses extend this enum without changing HB itself.
type MemorySyncKind uint8

const (
	MemorySyncInvalid MemorySyncKind = iota
	MemorySyncReleaseAcquire
)

// MemorySyncEdge is a validated synchronizes-with edge.
type MemorySyncEdge struct {
	From MemoryEventID
	To   MemoryEventID
	Kind MemorySyncKind
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
	ErrMemoryEventOutOfRange  = errors.New("memory event id out of range")
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

// Validate checks the structural execution witness. It is deliberately
// separate from graph queries so hot verification/model-checking loops can
// validate once and reuse allocation-free reachability operations many times.
func (x MemoryExecution) Validate() error {
	for i, event := range x.Events {
		if !legalEventOrder(event) {
			return fmt.Errorf("event %d has illegal atomic/non-atomic order", i)
		}
		if event.Access == MemoryAccessFence {
			if !event.Atomic || event.HasReadsFrom {
				return fmt.Errorf("event %d has invalid fence shape", i)
			}
		} else if event.Access == MemoryAccessNone {
			return fmt.Errorf("event %d has no memory access", i)
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
	}

	// Sequence numbers define per-thread source order and must be unique.
	for i := 0; i < len(x.Events); i++ {
		for j := i + 1; j < len(x.Events); j++ {
			if x.Events[i].Thread == x.Events[j].Thread && x.Events[i].Sequence == x.Events[j].Sequence {
				return fmt.Errorf("events %d and %d duplicate thread sequence", i, j)
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
		switch edge.Kind {
		case MemorySyncReleaseAcquire:
			from := x.Events[edge.From]
			to := x.Events[edge.To]
			if !from.Atomic || !from.Access.writes() || !releaseLike(from.Order) {
				return fmt.Errorf("sync edge %d source is not a release-like atomic write", i)
			}
			if !to.Atomic || !to.Access.reads() || !acquireLike(to.Order) {
				return fmt.Errorf("sync edge %d target is not an acquire-like atomic read", i)
			}
			if from.Location != to.Location || !to.HasReadsFrom || to.ReadsFrom != edge.From {
				return fmt.Errorf("sync edge %d is not witnessed by reads-from on one location", i)
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
