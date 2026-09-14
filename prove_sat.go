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

func certificateRung(model *compiler.SemanticModel, results []prove.Result, run bool, cnfDir string, conflicts int, stdout io.Writer) []prove.Result {
	// The solver: the one written in Oak (prove/solver/sat.oak) behind the
	// clause engine written in Oak (prove/solver/cnf.oak), unless
	// OAK_SAT_SOLVER names an external one, which then takes the Go clause
	// engine's clauses; a named solver that is not found skips the rung by
	// name.
	var solve func(asm.CNF) (prove.SATOutcome, error)
	oakPath := false
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
			oakPath = true
			solve = func(cnf asm.CNF) (prove.SATOutcome, error) { return runOakSATWithin(cnf, conflicts) }
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
		if oakPath {
			results[i] = oakClauseRung(model, r, cnf, conflicts)
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

// oakClauseRung decides one row through the Oak path: the problem table
// lowered to clauses in Oak, solved in Oak, the certificate checked in Go
// and in Oak against the Oak formula, a model confirmed against it. The
// Go clause engine's lowering (goCNF) is the cross-check: equal variable
// and clause counts say the two engines agree; otherwise the Go clauses
// are solved too and the verdicts must match.
func oakClauseRung(model *compiler.SemanticModel, r prove.Result, goCNF asm.CNF, conflicts int) prove.Result {
	problem, reason, err := prove.ProblemFor(model, r.Name, "interleaved", asm.NodeBudget)
	if err != nil || reason != "" {
		return r
	}
	run, err := runOakClausesWithin(problem, conflicts)
	if err != nil {
		r.Detail += "; the certificate rung gave no verdict (" + err.Error() + ")"
		return r
	}
	if run.Constant != 0 {
		kind := asm.DecisionRefuted
		message := "the obligation folds to true in Oak's clause engine"
		if run.Constant == 1 {
			kind = asm.DecisionProven
			message = "at the bit level (the obligation folds to a constant, lowered in Oak)"
		}
		if goCNF.Settled == nil || (goCNF.Settled.Kind == asm.DecisionProven) != (kind == asm.DecisionProven) {
			r.Status = prove.Open
			r.Detail = fmt.Sprintf("the clause engines disagree: Oak folds the obligation to a constant (%s), Go does not", message)
			return r
		}
		return agreeSettled(r, &asm.Decision{Kind: kind, Message: message})
	}
	engines := ""
	switch {
	case goCNF.Settled == nil && goCNF.Variables == run.Variables && goCNF.Clauses == run.Clauses:
		engines = "; the Go clause engine agrees"
	default:
		// The lowerings differ in shape: solve the Go clauses too and
		// require the same verdict.
		goOutcome, err := runOakSATWithin(goCNF, conflicts)
		switch {
		case goCNF.Settled != nil:
			engines = fmt.Sprintf("; the Go clause engine folds the obligation to a constant where Oak's has %d clauses", run.Clauses)
		case err != nil:
			engines = fmt.Sprintf("; the Go clause engine's clauses (%d variables, %d clauses) gave no verdict (%v)", goCNF.Variables, goCNF.Clauses, err)
		case goOutcome.Unsatisfiable == run.Outcome.Unsatisfiable:
			engines = fmt.Sprintf("; the Go clause engine agrees on the verdict (%d variables, %d clauses against %d, %d)", goCNF.Variables, goCNF.Clauses, run.Variables, run.Clauses)
		default:
			r.Status = prove.Open
			r.Detail = fmt.Sprintf("the clause engines disagree: Oak's clauses are %s, Go's are %s", verdictWord(run.Outcome), verdictWord(goOutcome))
			return r
		}
	}
	switch {
	case run.Outcome.Unsatisfiable:
		checked, goErr := prove.CheckLRAT(run.Formula, run.Outcome.Certificate)
		oak, oakErr := runOakLRAT(run.Formula, run.Outcome.Certificate)
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
			r.Detail += "; the Oak solver's certificate was refused, so its verdict does not count (" + refusal + ")"
			return r
		}
		note := fmt.Sprintf("an LRAT certificate of %d steps, lowered to clauses in Oak, checked in Go and in Oak%s", checked.Additions+checked.Deletions, engines)
		switch r.Status {
		case prove.Decided:
			r.Detail += "; the certificate rung agrees (" + note + ")"
		case prove.Refuted:
			r.Status = prove.Open
			r.Detail = fmt.Sprintf("the certificate rung disagrees with the ladder: the ladder refuted it (%s), the Oak solver proved it (%s)", r.Detail, note)
		default:
			r.Status = prove.Decided
			r.Detail = "at the bit level (" + note + ")"
		}
	case run.Outcome.Satisfiable:
		holds, err := prove.ModelSatisfies(run.Formula, run.Outcome.Model)
		if err != nil || !holds {
			r.Detail += "; the Oak solver's model does not satisfy its own clauses, so its verdict does not count"
			return r
		}
		var set []uint32
		for _, lit := range run.Outcome.Model {
			if lit > 0 {
				if variable, isInput := run.Inputs[lit]; isInput {
					set = append(set, variable)
				}
			}
		}
		counterexample := problem.Counterexample(set)
		switch r.Status {
		case prove.Refuted:
			r.Detail += "; the certificate rung agrees (counterexample " + counterexample + ", lowered to clauses in Oak" + engines + ")"
		case prove.Decided:
			r.Status = prove.Open
			r.Detail = fmt.Sprintf("the certificate rung disagrees with the ladder: the ladder decided it (%s), the Oak solver's model %s refutes its clauses", r.Detail, counterexample)
		default:
			r.Status = prove.Refuted
			r.Detail = "counterexample " + counterexample + " (the Oak solver's model over clauses lowered in Oak, confirmed against them" + engines + ")"
		}
	}
	return r
}

func verdictWord(outcome prove.SATOutcome) string {
	if outcome.Unsatisfiable {
		return "unsatisfiable"
	}
	if outcome.Satisfiable {
		return "satisfiable"
	}
	return "undecided"
}
