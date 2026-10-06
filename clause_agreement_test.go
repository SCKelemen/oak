package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/prove"
)

const (
	agreementUnsat = "p cnf 2 2\n1 0\n-1 0\n"
	agreementOther = "p cnf 2 2\n2 0\n-2 0\n"
	agreementSat   = "p cnf 2 2\n1 0\n1 0\n"
	agreementProof = "3 0 1 2 0\n"
)

func TestClauseAgreementPolicy(t *testing.T) {
	// Fixed admission table for every valid kind plus low/high invalid kinds.
	kinds := []clauseEvidence{clauseUnknown, clauseSAT, clauseUNSAT, 3, 255}
	want := [][]clauseAgreement{
		{clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable},
		{clauseUnavailable, clauseAgrees, clauseDisagrees, clauseUnavailable, clauseUnavailable},
		{clauseUnavailable, clauseDisagrees, clauseAgrees, clauseUnavailable, clauseUnavailable},
		{clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable},
		{clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable, clauseUnavailable},
	}
	var source strings.Builder
	source.WriteString("import Oak.ClauseAgreement\n\n")
	for i, expected := range kinds {
		for j, observed := range kinds {
			got := compareClauseEvidence(expected, observed)
			if got != want[i][j] {
				t.Fatalf("compare(%d,%d) = %d, want %d", expected, observed, got, want[i][j])
			}
			fmt.Fprintf(&source, "example : Oak.ClauseAgreement.compare %d %d = %d := by decide\n", expected, observed, got)
		}
	}
	t.Run("Lean", func(t *testing.T) {
		lake, err := exec.LookPath("lake")
		if err != nil {
			if os.Getenv("OAK_REQUIRE_CLAUSE_AGREEMENT_LEAN") != "" {
				t.Fatal("lake is required for the clause-agreement policy gate")
			}
			t.Skip("lake not on PATH; formal CI requires the Lean replay")
		}
		path := filepath.Join(t.TempDir(), "ClauseAgreementPins.lean")
		if err := os.WriteFile(path, []byte(source.String()), 0600); err != nil {
			t.Fatal(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 3*time.Minute)
		defer cancel()
		for _, args := range [][]string{{"build", "Oak.ClauseAgreement"}, {"env", "lean", path}} {
			cmd := exec.CommandContext(ctx, lake, args...)
			cmd.Dir = filepath.Join("spec", "lean")
			if out, err := cmd.CombinedOutput(); err != nil {
				t.Fatalf("Lean clause agreement: %v (%v)\n%s", err, ctx.Err(), out)
			}
		}
	})
}

func agreementCNF(text string) asm.CNF {
	return asm.CNF{Text: text, Variables: 2, Clauses: 2}
}

func TestClauseAgreementRequiresCheckedEvidence(t *testing.T) {
	for _, test := range []struct {
		name       string
		formula    string
		observed   clauseEvidence
		outcome    prove.SATOutcome
		solveError error
		oakCheck   OakLRATVerdict
		checkError error
		want       clauseAgreement
		checkCalls int
	}{
		{"same counts different truth", agreementSat, clauseUNSAT, prove.SATOutcome{Satisfiable: true, Model: []int{1}}, nil, OakLRATVerdict{}, nil, clauseDisagrees, 0},
		{"checked UNSAT", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{Additions: 1}, nil, clauseAgrees, 1},
		{"bare UNSAT", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"bad UNSAT proof", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: "3 0 1 0\n"}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"UNSAT proof for SAT formula", agreementSat, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"Oak checker refusal", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{Status: 1}, nil, clauseUnavailable, 1},
		{"Oak checker error", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{}, errors.New("checker failed"), clauseUnavailable, 1},
		{"addition count mismatch", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 1},
		{"deletion count mismatch", agreementOther, clauseUNSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{Additions: 1, Deletions: 1}, nil, clauseUnavailable, 1},
		{"SAT is not UNKNOWN", agreementSat, clauseSAT, prove.SATOutcome{}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"both flags", agreementSat, clauseSAT, prove.SATOutcome{Satisfiable: true, Unsatisfiable: true}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"bad model", agreementSat, clauseSAT, prove.SATOutcome{Satisfiable: true, Model: []int{-1}}, nil, OakLRATVerdict{}, nil, clauseUnavailable, 0},
		{"checked SAT", agreementSat, clauseSAT, prove.SATOutcome{Satisfiable: true, Model: []int{1}}, nil, OakLRATVerdict{}, nil, clauseAgrees, 0},
		{"opposite checked UNSAT", agreementOther, clauseSAT, prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil, OakLRATVerdict{Additions: 1}, nil, clauseDisagrees, 1},
		{"budget exhaustion", agreementOther, clauseUNSAT, prove.SATOutcome{}, errors.New("conflict budget"), OakLRATVerdict{}, nil, clauseUnavailable, 0},
	} {
		t.Run(test.name, func(t *testing.T) {
			solves, checks := 0, 0
			solve := func(cnf asm.CNF) (prove.SATOutcome, error) {
				solves++
				if cnf.Text != test.formula {
					t.Fatal("did not solve the independent formula")
				}
				return test.outcome, test.solveError
			}
			check := func(formula, proof string) (OakLRATVerdict, error) {
				checks++
				if formula != test.formula || proof != test.outcome.Certificate {
					t.Fatal("did not check the independent formula and proof")
				}
				return test.oakCheck, test.checkError
			}
			got, detail := checkClauseAgreement(agreementCNF(test.formula), agreementUnsat, test.observed, solve, check)
			if got != test.want || solves != 1 || checks != test.checkCalls {
				t.Fatalf("agreement=%d want=%d solves=%d checks=%d want=%d: %s", got, test.want, solves, checks, test.checkCalls, detail)
			}
		})
	}
}

func TestClauseAgreementExactFormulaAndConstants(t *testing.T) {
	solve := func(asm.CNF) (prove.SATOutcome, error) {
		t.Fatal("unexpected solver invocation")
		return prove.SATOutcome{}, nil
	}
	check := func(string, string) (OakLRATVerdict, error) {
		t.Fatal("unexpected checker invocation")
		return OakLRATVerdict{}, nil
	}
	for _, formula := range []string{agreementUnsat, "c different formatting\np cnf 2 2\n 1\n0\n-1 0\n"} {
		cnf := agreementCNF(formula)
		// Redundant summary dimensions cannot replace the actual formula.
		cnf.Variables, cnf.Clauses = 100, 200
		got, detail := checkClauseAgreement(cnf, agreementUnsat, clauseUNSAT, solve, check)
		if got != clauseAgrees || !strings.Contains(detail, "exact ordered formula") {
			t.Fatalf("same database: %d %s", got, detail)
		}
	}
	for _, test := range []struct {
		kind asm.DecisionKind
		want clauseAgreement
	}{{asm.DecisionProven, clauseAgrees}, {asm.DecisionRefuted, clauseDisagrees}, {asm.DecisionUndecided, clauseUnavailable}} {
		got, _ := checkClauseAgreement(asm.CNF{Settled: &asm.Decision{Kind: test.kind}}, agreementUnsat, clauseUNSAT, solve, check)
		if got != test.want {
			t.Fatalf("constant %v: %d want %d", test.kind, got, test.want)
		}
	}
	for _, formula := range []string{"invalid", "p cnf 2 1\n3 0\n"} {
		got, _ := checkClauseAgreement(agreementCNF(formula), agreementUnsat, clauseUNSAT, solve, check)
		if got != clauseUnavailable {
			t.Fatalf("malformed formula accepted: %q", formula)
		}
	}
	for _, evidence := range []clauseEvidence{clauseUnknown, 255} {
		got, _ := checkClauseAgreement(agreementCNF(agreementUnsat), agreementUnsat, evidence, solve, check)
		if got != clauseUnavailable {
			t.Fatalf("unchecked Oak evidence %d accepted", evidence)
		}
	}
}

func TestClauseAgreementUsesRealOakChecker(t *testing.T) {
	got, detail := checkClauseAgreement(agreementCNF(agreementOther), agreementUnsat, clauseUNSAT,
		func(cnf asm.CNF) (prove.SATOutcome, error) { return runOakSAT(cnf) }, runOakLRAT)
	if got != clauseAgrees {
		t.Fatalf("independent formula was not certified: %d %s", got, detail)
	}
}

func TestClauseAgreementCannotPromoteUncheckedRows(t *testing.T) {
	record, err := prove.EncodeLRATWords(agreementUnsat, agreementProof)
	if err != nil {
		t.Fatal(err)
	}
	run := OakClauseRun{Formula: agreementUnsat, Variables: 2, Clauses: 2,
		Outcome: prove.SATOutcome{Unsatisfiable: true}, Record: record,
		Checked: true, OakCheck: OakLRATVerdict{Additions: 1}}
	neverCheck := func(string, string) (OakLRATVerdict, error) {
		t.Fatal("an uncheckable proof reached the Oak checker")
		return OakLRATVerdict{}, nil
	}
	for _, status := range []prove.Status{prove.Open, prove.Decided, prove.Refuted} {
		r := prove.Result{Name: "claim", Status: status, Detail: "prior evidence"}
		got := reconcileOakClauseRun(r, agreementCNF(agreementOther), asm.Problem{}, run,
			func(asm.CNF) (prove.SATOutcome, error) { return prove.SATOutcome{Unsatisfiable: true}, nil }, neverCheck)
		if got.Status != status || !strings.Contains(got.Detail, "no checked cross-engine verdict") {
			t.Fatalf("unconfirmed fallback changed %v: %+v", status, got)
		}
		// Same-sized but satisfiable Go clauses conflict with the Oak proof.
		got = reconcileOakClauseRun(r, agreementCNF(agreementSat), asm.Problem{}, run,
			func(asm.CNF) (prove.SATOutcome, error) {
				return prove.SATOutcome{Satisfiable: true, Model: []int{1}}, nil
			}, neverCheck)
		if got.Status != prove.Open || !strings.Contains(got.Detail, "clause engines disagree") {
			t.Fatalf("same counts hid a checked contradiction: %+v", got)
		}
	}
	// Refuse the primary certificate before attempting to cross-check it.
	run.Record = nil
	got := reconcileOakClauseRun(prove.Result{Status: prove.Open}, agreementCNF(agreementOther), asm.Problem{}, run,
		func(asm.CNF) (prove.SATOutcome, error) {
			t.Fatal("unchecked Oak certificate reached cross-check")
			return prove.SATOutcome{}, nil
		}, neverCheck)
	if got.Status != prove.Open || !strings.Contains(got.Detail, "certificate was refused") {
		t.Fatalf("unchecked primary certificate accepted: %+v", got)
	}
	for _, constant := range []int{2, 3} {
		got := reconcileOakClauseRun(prove.Result{Status: prove.Open},
			asm.CNF{Settled: &asm.Decision{Kind: asm.DecisionUndecided}}, asm.Problem{}, OakClauseRun{Constant: constant}, nil, nil)
		if got.Status != prove.Open {
			t.Fatalf("unknown constant evidence promoted the row: %+v", got)
		}
	}
}

func TestClauseAgreementPromotesOnlyCheckedRows(t *testing.T) {
	record, err := prove.EncodeLRATWords(agreementUnsat, agreementProof)
	if err != nil {
		t.Fatal(err)
	}
	proved := OakClauseRun{Formula: agreementUnsat, Outcome: prove.SATOutcome{Unsatisfiable: true},
		Record: record, Checked: true, OakCheck: OakLRATVerdict{Additions: 1}}
	for _, formula := range []string{agreementUnsat, agreementOther} {
		got := reconcileOakClauseRun(prove.Result{Status: prove.Open}, agreementCNF(formula), asm.Problem{}, proved,
			func(cnf asm.CNF) (prove.SATOutcome, error) {
				if formula == agreementUnsat || cnf.Text != formula {
					t.Fatal("exact formula did not reuse its checked certificate")
				}
				return prove.SATOutcome{Unsatisfiable: true, Certificate: agreementProof}, nil
			}, func(formula, proof string) (OakLRATVerdict, error) {
				return OakLRATVerdict{Additions: 1}, nil
			})
		if got.Status != prove.Decided || !strings.Contains(got.Detail, "an LRAT certificate") {
			t.Fatalf("checked evidence did not close the row: %+v", got)
		}
	}
	// Driver-only fixture: source-term evaluation has no symbolic terms here.
	// The existing theorem integration suite covers real term confirmation.
	model := OakClauseRun{Formula: agreementSat, Outcome: prove.SATOutcome{Satisfiable: true, Model: []int{1}}}
	got := reconcileOakClauseRun(prove.Result{Status: prove.Open}, agreementCNF(agreementSat), asm.Problem{}, model, nil, nil)
	if got.Status != prove.Refuted {
		t.Fatalf("checked exact-formula model did not refute: %+v", got)
	}
	// A SAT row cannot agree with a fallback that returned no outcome, even
	// though both of their raw Unsatisfiable flags are false.
	got = reconcileOakClauseRun(prove.Result{Status: prove.Open}, agreementCNF("p cnf 2 1\n1 0\n"), asm.Problem{}, model,
		func(asm.CNF) (prove.SATOutcome, error) { return prove.SATOutcome{}, nil }, nil)
	if got.Status != prove.Open || !strings.Contains(got.Detail, "no checked cross-engine verdict") {
		t.Fatalf("UNKNOWN was mistaken for SAT agreement: %+v", got)
	}
}
