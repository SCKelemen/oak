package main

import (
	"bytes"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/prove"
)

func TestSelfProveCrossCheckRequiresCompleteUniqueRows(t *testing.T) {
	results := []prove.Result{
		{Name: "identity", Status: prove.Decided},
		{Name: "Quantum: guards of tick from Running", Status: prove.Open, Advisory: true},
	}
	identity := "decided   identity: checked\n"
	advisory := "open      Quantum: guards of tick from Running: unsupported\n"
	for _, tc := range []struct {
		name, rows, diagnostic string
		want                   bool
	}{
		{"complete", identity + advisory + "oak prove: 1 decided, 1 open\n", "agrees on 2 of 2 rows", true},
		{"reordered", advisory + identity, "agrees on 2 of 2 rows", true},
		{"empty", "", "missing Oak result for identity", false},
		{"summary only", "oak prove: 2 decided\n", "missing Oak result for identity", false},
		{"truncated", identity, "missing Oak result for Quantum", false},
		{"duplicate", identity + identity + advisory, "duplicate Oak result for identity", false},
		{"unknown", identity + advisory + "decided   stale: checked\n", "unrecognized Oak result row", false},
		{"malformed spacing", "decided identity: checked\n" + advisory, "unrecognized Oak result row", false},
		{"unknown status", "bogus     identity: checked\n" + advisory, "Go decided, Oak bogus", false},
		{"disagreement", "refuted   identity: counterexample\n" + advisory, "Go decided, Oak refuted", false},
		{"conflicting duplicate", identity + "refuted   identity: counterexample\n" + advisory, "duplicate Oak result for identity", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var out bytes.Buffer
			if got := compareSelfProveRows(tc.rows, results, &out); got != tc.want {
				t.Fatalf("accepted=%v, want %v: %s", got, tc.want, &out)
			}
			if !strings.Contains(out.String(), tc.diagnostic) {
				t.Fatalf("missing diagnostic %q: %s", tc.diagnostic, &out)
			}
		})
	}
}

func TestSelfProveCrossCheckRejectsDuplicateExpectedNames(t *testing.T) {
	results := []prove.Result{{Name: "law", Status: prove.Decided}, {Name: "law", Status: prove.Decided}}
	var out bytes.Buffer
	if compareSelfProveRows("decided   law: checked\n", results, &out) || !strings.Contains(out.String(), "duplicate Go result") {
		t.Fatalf("duplicate expected names accepted: %s", &out)
	}
}

func TestSelfProveCrossCheckUsesLongestAdvisoryName(t *testing.T) {
	results := []prove.Result{{Name: "Quantum", Status: prove.Decided}, {Name: "Quantum: guards", Status: prove.Open}}
	var out bytes.Buffer
	if !compareSelfProveRows("open      Quantum: guards: unsupported\ndecided   Quantum: checked\n", results, &out) {
		t.Fatalf("advisory name was misidentified: %s", &out)
	}
}
