package asm

import "fmt"

// cnfObligationOutcome names the four ways exportTermCNF can settle or emit
// the Boolean obligation. The producer still chooses the result; the audit
// below independently derives the expected choice from the memoized roots.
type cnfObligationOutcome uint8

const (
	cnfObligationTrapAlways cnfObligationOutcome = iota
	cnfObligationClaimFalse
	cnfObligationConstantProven
	cnfObligationFormula
)

type cnfObligationCounts struct {
	variables int
	clauses   int
	inputs    int
	gates     int
	gateMemo  int
	termMemo  int
	owners    int
	selects   int
	exceeded  bool
}

func snapshotCNFObligationCounts(bl *blaster) cnfObligationCounts {
	return cnfObligationCounts{
		variables: bl.cnf.variables,
		clauses:   len(bl.cnf.clauses),
		inputs:    len(bl.cnf.inputs),
		gates:     len(bl.cnf.gates),
		gateMemo:  len(bl.cnf.memo),
		termMemo:  len(bl.memo),
		owners:    len(bl.owners),
		selects:   len(bl.selects),
		exceeded:  bl.cnf.exceeded,
	}
}

// validateCNFObligation replays the supplied Boolean term keys through blast's
// term memo and independently checks the producer's final outcome. Replaying
// a completed root must neither allocate another gate nor change any blaster
// bookkeeping; this makes the supplied term keys plus the completed memo,
// rather than the producer's accumulated slice, the authority for final-clause
// assembly.
func validateCNFObligation(bl *blaster, traps []*term, claim *term, outcome cnfObligationOutcome, obligation []int) error {
	if bl == nil || bl.cnf == nil {
		return fmt.Errorf("CNF blaster is nil")
	}
	before := snapshotCNFObligationCounts(bl)

	trapAlways := false
	symbolicTraps := 0
	for index, trap := range traps {
		root, err := replayCNFObligationRoot(bl, trap)
		if err != nil {
			return fmt.Errorf("trap %d: %w", index, err)
		}
		switch root {
		case bddFalse:
		case bddTrue:
			trapAlways = true
		default:
			symbolicTraps++
		}
	}
	claimRoot, err := replayCNFObligationRoot(bl, claim)
	if err != nil {
		return fmt.Errorf("claim: %w", err)
	}
	if snapshotCNFObligationCounts(bl) != before {
		return fmt.Errorf("replaying the obligation changed the completed CNF builder")
	}

	expected := cnfObligationFormula
	switch {
	case trapAlways:
		expected = cnfObligationTrapAlways
	case claimRoot == bddFalse:
		expected = cnfObligationClaimFalse
	case claimRoot == bddTrue && symbolicTraps == 0:
		expected = cnfObligationConstantProven
	}
	if outcome != expected {
		return fmt.Errorf("producer outcome %d does not match replayed outcome %d", outcome, expected)
	}

	// Stream the expected roots directly against the producer's slice. This also
	// checks the filtered trap sequence when a constant trap or claim settles the
	// result. A second memo-only traversal avoids retaining another input-sized
	// slice.
	cursor := 0
	for index, trap := range traps {
		root, err := replayCNFObligationRoot(bl, trap)
		if err != nil {
			return fmt.Errorf("trap %d on final-clause replay: %w", index, err)
		}
		if root == bddFalse || root == bddTrue {
			continue
		}
		if cursor >= len(obligation) {
			return fmt.Errorf("final obligation ends before symbolic trap %d", index)
		}
		if obligation[cursor] != root {
			return fmt.Errorf("final obligation edge %d is %d, want trap %d root %d",
				cursor, obligation[cursor], index, root)
		}
		cursor++
	}
	if outcome == cnfObligationFormula && claimRoot != bddTrue {
		if cursor >= len(obligation) {
			return fmt.Errorf("final obligation ends before the negated claim root")
		}
		want := claimRoot ^ 1
		if obligation[cursor] != want {
			return fmt.Errorf("final obligation edge %d is %d, want negated claim root %d",
				cursor, obligation[cursor], want)
		}
		cursor++
	}
	if cursor != len(obligation) {
		return fmt.Errorf("final obligation has %d trailing edges", len(obligation)-cursor)
	}
	if snapshotCNFObligationCounts(bl) != before {
		return fmt.Errorf("replaying the final obligation changed the completed CNF builder")
	}
	return nil
}

func replayCNFObligationRoot(bl *blaster, root *term) (int, error) {
	if root == nil {
		return 0, fmt.Errorf("term is nil")
	}
	bits := bl.blast(root)
	if len(bits) != 1 {
		return 0, fmt.Errorf("replay produced %d bits, want exactly one", len(bits))
	}
	if bl.exceeded() {
		return 0, fmt.Errorf("replay exceeded the clause budget")
	}
	edge := bits[0]
	if edge != bddFalse && edge != bddTrue && (edge < 2 || edge>>1 > bl.cnf.variables) {
		return 0, fmt.Errorf("replay root edge %d is outside the allocated range", edge)
	}
	return edge, nil
}
