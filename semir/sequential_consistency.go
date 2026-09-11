package semir

import "fmt"

// SequentialConsistencyWitness is the global total order over all seq-cst
// events in one execution. Position in Order is semantic SC rank. Keeping this
// witness separate from MemoryEvent prevents the global relation from being
// confused with program order, reads-from, or per-location modification order.
// The caller owns the slice; validation allocates no hidden storage.
type SequentialConsistencyWitness struct {
	Order []MemoryEventID
}

func isSeqCstEvent(event MemoryEvent) bool {
	return event.Atomic && event.Order == MemoryOrderSeqCst
}

// Position returns the SC rank of event. Linear lookup is intentional in the
// reference verifier: bounded, allocation-free, and easy to audit. Optimized
// indexes may later refine this representation if measurements justify them.
func (s SequentialConsistencyWitness) Position(event MemoryEventID) (int, bool) {
	for i := range s.Order {
		if s.Order[i] == event {
			return i, true
		}
	}
	return 0, false
}

func (s SequentialConsistencyWitness) Before(a, b MemoryEventID) bool {
	pa, oka := s.Position(a)
	pb, okb := s.Position(b)
	return oka && okb && pa < pb
}

func (s SequentialConsistencyWitness) validateMembership(x MemoryExecution) error {
	seqCstCount := 0
	for i := range x.Events {
		if isSeqCstEvent(x.Events[i]) {
			seqCstCount++
		}
	}
	if len(s.Order) != seqCstCount {
		return fmt.Errorf("seq-cst witness has %d entries for %d seq-cst events", len(s.Order), seqCstCount)
	}

	for i, id := range s.Order {
		if int(id) >= len(x.Events) {
			return fmt.Errorf("seq-cst rank %d references out-of-range event %d", i, id)
		}
		if !isSeqCstEvent(x.Events[id]) {
			return fmt.Errorf("seq-cst rank %d references non-seq-cst event %d", i, id)
		}
		for j := i + 1; j < len(s.Order); j++ {
			if s.Order[j] == id {
				return fmt.Errorf("seq-cst event %d appears more than once", id)
			}
		}
	}

	for id := range x.Events {
		if !isSeqCstEvent(x.Events[id]) {
			continue
		}
		if _, ok := s.Position(MemoryEventID(id)); !ok {
			return fmt.Errorf("seq-cst event %d is absent from global order", id)
		}
	}
	return nil
}

// visibleWriteSkipped reports whether a seq-cst read observes source while a
// later modification is already ordered before the read by HB or by the global
// SC order. Such an execution would allow the read to skip a write that is
// already semantically visible to it.
func (s SequentialConsistencyWitness) visibleWriteSkipped(
	x MemoryExecution,
	read MemoryEventID,
	source MemoryEventID,
	workspace MemoryWorkspace,
) (bool, error) {
	sourceEvent := x.Events[source]
	for candidate := range x.Events {
		candidateID := MemoryEventID(candidate)
		write := x.Events[candidate]
		if candidateID == source || !write.Atomic || !write.Access.writes() ||
			!write.HasModification || write.Location != sourceEvent.Location ||
			write.Modification <= sourceEvent.Modification {
			continue
		}

		hb, err := x.HappensBefore(candidateID, read, workspace)
		if err != nil {
			return false, err
		}
		if hb {
			return true, nil
		}
		if isSeqCstEvent(write) && s.Before(candidateID, read) {
			return true, nil
		}
	}
	return false, nil
}

// initialWriteSkipped reports whether an SC read claiming the implicit initial
// value has any represented write already visible before it by HB or SC order.
func (s SequentialConsistencyWitness) initialWriteSkipped(
	x MemoryExecution,
	read MemoryEventID,
	workspace MemoryWorkspace,
) (bool, error) {
	readEvent := x.Events[read]
	for candidate := range x.Events {
		candidateID := MemoryEventID(candidate)
		write := x.Events[candidate]
		if !write.Atomic || !write.Access.writes() || write.Location != readEvent.Location {
			continue
		}
		hb, err := x.HappensBefore(candidateID, read, workspace)
		if err != nil {
			return false, err
		}
		if hb || (isSeqCstEvent(write) && s.Before(candidateID, read)) {
			return true, nil
		}
	}
	return false, nil
}

// ValidateSequentialConsistency validates Oak's global SC witness after the
// core execution graph. It uses only caller-owned MemoryWorkspace and bounded
// scans over Events/Order; the success path performs no hidden allocation.
//
// Constraints:
//  1. every and only seq-cst event appears exactly once in S;
//  2. S is consistent with happens-before among seq-cst events;
//  3. S is consistent with per-location modification order among seq-cst
//     writes/RMWs;
//  4. an SC read/RMW may not skip a later modification that is already visible
//     before it through HB or the SC order;
//  5. an SC read of the implicit initial value may not have any visible write
//     before it.
func (x MemoryExecution) ValidateSequentialConsistency(
	s SequentialConsistencyWitness,
	workspace MemoryWorkspace,
) error {
	if err := x.Validate(); err != nil {
		return err
	}
	if len(workspace.Visited) < len(x.Events) || len(workspace.Stack) < len(x.Events) {
		return ErrMemoryWorkspaceTooSmall
	}
	if err := s.validateMembership(x); err != nil {
		return err
	}

	// Since s.Order is a concrete sequence, totality/transitivity are by
	// construction. Reject any pair whose required HB or modification direction
	// contradicts that sequence.
	for earlier := 0; earlier < len(s.Order); earlier++ {
		for later := earlier + 1; later < len(s.Order); later++ {
			a := s.Order[earlier]
			b := s.Order[later]

			reverseHB, err := x.HappensBefore(b, a, workspace)
			if err != nil {
				return err
			}
			if reverseHB {
				return fmt.Errorf("seq-cst order places event %d before happens-before predecessor %d", a, b)
			}
			if x.ModificationBefore(b, a) {
				return fmt.Errorf("seq-cst order reverses modification order between events %d and %d", a, b)
			}
		}
	}

	for _, readID := range s.Order {
		read := x.Events[readID]
		if !read.Access.reads() {
			continue
		}
		if read.HasReadsFrom {
			source := read.ReadsFrom
			if isSeqCstEvent(x.Events[source]) && !s.Before(source, readID) {
				return fmt.Errorf("seq-cst read %d observes seq-cst write %d that is not SC-before it", readID, source)
			}
			skipped, err := s.visibleWriteSkipped(x, readID, source, workspace)
			if err != nil {
				return err
			}
			if skipped {
				return fmt.Errorf("seq-cst read %d skips a later visible modification", readID)
			}
			continue
		}

		skipped, err := s.initialWriteSkipped(x, readID, workspace)
		if err != nil {
			return err
		}
		if skipped {
			return fmt.Errorf("seq-cst read %d observes initial value after a visible write", readID)
		}
	}
	return nil
}
