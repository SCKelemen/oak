package main

// The certificate rung of `oak prove` (docs/spec/125-verification.md §3,
// §4): every bit-level obligation as clauses (asm.ExportCNF), an external
// SAT solver run on them when one is installed, and its LRAT certificate
// checked by the Go checker (prove/lrat.go) and the checker written in
// Oak (prove/solver/lrat.oak) before a row changes. The solver is
// untrusted: an unsatisfiable verdict counts only with an accepted
// certificate, a model only when the clause engine's own evaluation
// confirms it is a counterexample. Where the ladder already decided, the
// rung is a cross-check, and a disagreement makes the row open naming
// both, as the Oak-solver cross-check does.

import (
	"fmt"
	"io"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

func certificateRung(model *compiler.SemanticModel, results []prove.Result, run bool, cnfDir string, stdout io.Writer) []prove.Result {
	// The solver: the one written in Oak (prove/solver/sat.oak) unless
	// OAK_SAT_SOLVER names an external one; a named solver that is not
	// found skips the rung by name.
	var solve func(asm.CNF) (prove.SATOutcome, error)
	if run {
		external, found := prove.FindSolver()
		switch {
		case !found:
			fmt.Fprintf(stdout, "oak prove: the certificate rung was skipped: OAK_SAT_SOLVER names %q, which is not on PATH\n", os.Getenv("OAK_SAT_SOLVER"))
		case external != "":
			solve = func(cnf asm.CNF) (prove.SATOutcome, error) {
				return prove.RunSolver(external, cnf, prove.SolverTimeout)
			}
		default:
			solve = runOakSAT
		}
	}
	if cnfDir != "" {
		if err := os.MkdirAll(cnfDir, 0o755); err != nil {
			fmt.Fprintf(stdout, "oak prove: -cnf %s: %v\n", cnfDir, err)
			cnfDir = ""
		}
	}
	// An invariant candidate's own row summarizes its generated base and
	// step obligations (prove/protocols.go); the predicate alone is not a
	// theorem over every state, so the rung reads the obligations instead.
	named := map[string]bool{}
	for _, r := range results {
		named[r.Name] = true
	}
	for i, r := range results {
		if r.Advisory || named[r.Name+"__base"] || named[r.Name+"__step"] {
			continue
		}
		cnf, reason, err := prove.CNFFor(model, r.Name)
		if err != nil || reason != "" {
			continue // not a bit-level obligation; the rung has nothing to say
		}
		if cnfDir != "" && cnf.Text != "" {
			if err := os.WriteFile(filepath.Join(cnfDir, r.Name+".cnf"), []byte(cnf.Text), 0o644); err != nil {
				fmt.Fprintf(stdout, "oak prove: -cnf %s: %v\n", r.Name, err)
			}
		}
		if solve == nil {
			continue
		}
		if cnf.Settled != nil {
			results[i] = agreeSettled(r, cnf.Settled)
			continue
		}
		outcome, err := solve(cnf)
		if err != nil {
			results[i].Detail += "; the certificate rung gave no verdict (" + err.Error() + ")"
			continue
		}
		switch {
		case outcome.Unsatisfiable:
			checked, goErr := prove.CheckLRAT(cnf.Text, outcome.Certificate)
			oak, oakErr := runOakLRAT(cnf.Text, outcome.Certificate)
			refusal := ""
			switch {
			case goErr != nil:
				refusal = "the Go checker: " + goErr.Error()
			case oakErr != nil:
				refusal = "the Oak checker: " + oakErr.Error()
			case oak.Status != 0:
				refusal = fmt.Sprintf("the Oak checker refused it (status %d)", oak.Status)
			}
			if refusal != "" {
				results[i].Detail += "; the SAT solver's certificate was refused, so its verdict does not count (" + refusal + ")"
				continue
			}
			note := fmt.Sprintf("an LRAT certificate of %d steps, checked in Go and in Oak", checked.Additions+checked.Deletions)
			switch r.Status {
			case prove.Decided:
				results[i].Detail += "; the certificate rung agrees (" + note + ")"
			case prove.Refuted:
				results[i].Status = prove.Open
				results[i].Detail = fmt.Sprintf("the certificate rung disagrees with the ladder: the ladder refuted it (%s), the SAT solver proved it (%s)", r.Detail, note)
			default:
				results[i].Status = prove.Decided
				results[i].Detail = "at the bit level (" + note + ")"
			}
		case outcome.Satisfiable:
			params := cnf.ModelParams(outcome.Model)
			if !cnf.Evaluate(params) {
				results[i].Detail += "; the SAT solver's model is not a counterexample under the clause engine's evaluation, so its verdict does not count"
				continue
			}
			counterexample := cnf.Counterexample(outcome.Model)
			switch r.Status {
			case prove.Refuted:
				results[i].Detail += "; the certificate rung agrees (counterexample " + counterexample + ")"
			case prove.Decided:
				results[i].Status = prove.Open
				results[i].Detail = fmt.Sprintf("the certificate rung disagrees with the ladder: the ladder decided it (%s), the SAT solver's model %s refutes it and the clause engine confirms it", r.Detail, counterexample)
			default:
				results[i].Status = prove.Refuted
				results[i].Detail = "counterexample " + counterexample + " (the SAT solver's model, confirmed by the clause engine)"
			}
		}
	}
	return results
}

// agreeSettled compares a ladder row with an obligation the clause engine
// folded to a constant.
func agreeSettled(r prove.Result, settled *asm.Decision) prove.Result {
	proven := settled.Kind == asm.DecisionProven
	switch {
	case proven && r.Status == prove.Decided:
		r.Detail += "; the certificate rung agrees (the obligation folds to a constant)"
	case !proven && r.Status == prove.Refuted:
		r.Detail += "; the certificate rung agrees (" + settled.Message + ")"
	case r.Status == prove.Decided || r.Status == prove.Refuted:
		r.Status = prove.Open
		r.Detail = fmt.Sprintf("the certificate rung disagrees with the ladder: the ladder said %s (%s), the clause engine folds the obligation to %s", r.Status, r.Detail, settled.Message)
	case proven:
		r.Status = prove.Decided
		r.Detail = settled.Message
	default:
		r.Status = prove.Refuted
		r.Detail = settled.Message
	}
	return r
}
