package main

import (
	"fmt"
	"regexp"
	"strings"
	"testing"
)

// Lean wraps long axiom lists across lines. Parse the complete bracketed list,
// and require exactly one report for every named theorem.
func cnfAxiomAudit(output, namespace string, names []string) error {
	expected := make(map[string]bool, len(names))
	for _, name := range names {
		expected[namespace+"."+name] = false
	}
	reports := regexp.MustCompile(`'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])`).FindAllStringSubmatch(output, -1)
	if len(reports) != len(names) {
		return fmt.Errorf("audited %d/%d theorem closures", len(reports), len(names))
	}
	for _, report := range reports {
		seen, known := expected[report[1]]
		if !known || seen {
			return fmt.Errorf("unexpected or duplicate theorem report: %s", report[1])
		}
		expected[report[1]] = true
		for _, axiom := range strings.Split(report[2], ",") {
			switch strings.TrimSpace(axiom) {
			case "", "propext", "Classical.choice", "Quot.sound":
			default:
				return fmt.Errorf("unexpected axiom in %s: %s", report[1], strings.TrimSpace(axiom))
			}
		}
	}
	return nil
}

func TestCNFAxiomAudit(t *testing.T) {
	for _, tc := range []struct {
		output string
		valid  bool
	}{
		{"'N.t' does not depend on any axioms", true},
		{"'N.t' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]", true},
		{"'N.t' depends on axioms: [propext,\n t._native.bv_decide.ax_1]", false},
		{"'N.t' depends on axioms: [propext,\n sorryAx]", false},
		{"'N.t' depends on axioms: [propext,", false},
		{"'N.other' does not depend on any axioms", false},
		{"'N.t' does not depend on any axioms\n'N.t' does not depend on any axioms", false},
	} {
		if err := cnfAxiomAudit(tc.output, "N", []string{"t"}); (err == nil) != tc.valid {
			t.Fatalf("valid=%t, error=%v, output=%q", tc.valid, err, tc.output)
		}
	}
}
