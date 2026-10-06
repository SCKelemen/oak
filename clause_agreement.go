package main

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/prove"
)

// These are checked evidence kinds, never the solver's unchecked status bits.
type clauseEvidence uint8

const (
	clauseUnknown clauseEvidence = iota
	clauseSAT
	clauseUNSAT
)

type clauseAgreement uint8

const (
	clauseUnavailable clauseAgreement = iota
	clauseAgrees
	clauseDisagrees
)

// The finite policy is mirrored in Oak.ClauseAgreement. Unknown or invalid
// kinds cannot agree, even when both sides report the same kind.
func compareClauseEvidence(expected, observed clauseEvidence) clauseAgreement {
	if (expected != clauseSAT && expected != clauseUNSAT) || (observed != clauseSAT && observed != clauseUNSAT) {
		return clauseUnavailable
	}
	if expected == observed {
		return clauseAgrees
	}
	return clauseDisagrees
}

type clauseSolver func(asm.CNF) (prove.SATOutcome, error)
type clauseProofChecker func(formula, certificate string) (OakLRATVerdict, error)

// checkedClauseOutcome validates the fallback solver's answer against the
// independently generated Go formula. A solver status alone is no evidence.
func checkedClauseOutcome(cnf asm.CNF, outcome prove.SATOutcome, checkOak clauseProofChecker) (clauseEvidence, error) {
	if outcome.Satisfiable == outcome.Unsatisfiable {
		return clauseUnknown, fmt.Errorf("the solver gave no unambiguous verdict")
	}
	if outcome.Satisfiable {
		holds, err := prove.ModelSatisfies(cnf.Text, outcome.Model)
		if err != nil {
			return clauseUnknown, err
		}
		if !holds {
			return clauseUnknown, fmt.Errorf("the solver's model does not satisfy the Go formula")
		}
		return clauseSAT, nil
	}
	goCheck, err := prove.CheckLRAT(cnf.Text, outcome.Certificate)
	if err != nil {
		return clauseUnknown, fmt.Errorf("the Go checker refused the fallback certificate: %w", err)
	}
	oakCheck, err := checkOak(cnf.Text, outcome.Certificate)
	if err != nil {
		return clauseUnknown, fmt.Errorf("the Oak checker: %w", err)
	}
	if oakCheck.Status != 0 {
		return clauseUnknown, fmt.Errorf("the Oak checker refused the fallback certificate (status %d)", oakCheck.Status)
	}
	if oakCheck.Additions != goCheck.Additions || oakCheck.Deletions != goCheck.Deletions {
		return clauseUnknown, fmt.Errorf("the checkers counted different fallback certificate steps")
	}
	return clauseUNSAT, nil
}

// checkClauseAgreement receives an already checked Oak result. Identical
// initial databases reuse its evidence. Different encodings require a checked
// answer for the Go database too; equal dimensions never establish identity.
// The callbacks keep subprocess execution separate from acceptance decisions.
func checkClauseAgreement(goCNF asm.CNF, oakFormula string, oakEvidence clauseEvidence, solve clauseSolver, checkOak clauseProofChecker) (clauseAgreement, string) {
	if compareClauseEvidence(oakEvidence, oakEvidence) != clauseAgrees {
		return clauseUnavailable, "the Oak clause engine supplied no checked verdict"
	}
	var goEvidence clauseEvidence
	if goCNF.Settled != nil {
		switch goCNF.Settled.Kind {
		case asm.DecisionProven:
			goEvidence = clauseUNSAT
		case asm.DecisionRefuted:
			goEvidence = clauseSAT
		}
		return compareClauseEvidence(goEvidence, oakEvidence), "the Go clause engine folds the obligation to a constant"
	}
	expected, err := prove.EncodeLRATWords(goCNF.Text, "")
	if err != nil {
		return clauseUnavailable, "the Go formula could not be read: " + err.Error()
	}
	observed, err := prove.EncodeLRATWords(oakFormula, "")
	if err != nil {
		return clauseUnavailable, "the Oak formula could not be read: " + err.Error()
	}
	if prove.LRATWordsMatchFormula(expected, observed) {
		return clauseAgrees, "the Go clause engine agrees on the exact ordered formula"
	}
	outcome, err := solve(goCNF)
	if err != nil {
		return clauseUnavailable, "the Go formula's solver gave no checked verdict: " + err.Error()
	}
	goEvidence, err = checkedClauseOutcome(goCNF, outcome, checkOak)
	if err != nil {
		return clauseUnavailable, "the Go formula's solver answer was refused: " + err.Error()
	}
	agreement := compareClauseEvidence(goEvidence, oakEvidence)
	if agreement == clauseDisagrees {
		return agreement, "the independently checked formula verdicts conflict"
	}
	return agreement, "the Go clause engine agrees on an independently checked verdict for its different formula"
}
