package lrat

import "testing"

func TestCheckWordsAgainstIndependentFormula(t *testing.T) {
	// A complete refutation of (x) AND (not x), written without the serializer.
	original := []uint32{Magic, 1, 2, 4, 6, 3, 2, 0, 1, 1, 1, 0, 0, 3, 0, 2, 1, 2}
	formula := "p cnf 1 2\n1 0\n-1 0\n"
	for _, tc := range []struct {
		name, formula string
		mutate        func([]uint32) []uint32
		accept        bool
	}{
		{"exact", formula, nil, true},
		{"whitespace", "c comment\np cnf 1 2\n1 0 -1 0\n", nil, true},
		{"different satisfiable obligation", "p cnf 1 2\n1 0\n1 0\n", nil, false},
		{"clause order", "p cnf 1 2\n-1 0\n1 0\n", nil, false},
		{"declared domain", "p cnf 2 2\n1 0\n-1 0\n", nil, false},
		{"malformed expected", "p cnf 1 2\n1 0\n", nil, false},
		{"hints are not identity", formula, func(w []uint32) []uint32 { w[5] = 0; w[6] = 0; w[7] = 99; return w }, true},
		{"invalid proof", formula, func(w []uint32) []uint32 { w[17] = 1; return w }, false},
		{"trailing word", formula, func(w []uint32) []uint32 { return append(w, 0) }, false},
		{"bad literal region", formula, func(w []uint32) []uint32 { w[3] = ^uint32(0); return w }, false},
		{"bad clause length", formula, func(w []uint32) []uint32 { w[8] = ^uint32(0); return w }, false},
		{"truncated", formula, func(w []uint32) []uint32 { return w[:7] }, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			w := append([]uint32(nil), original...)
			if tc.mutate != nil {
				w = tc.mutate(w)
			}
			_, err := CheckWordsAgainst(tc.formula, w)
			if (err == nil) != tc.accept {
				t.Fatalf("accept=%v, err=%v", tc.accept, err)
			}
		})
	}
}

func TestCheckWordsAgainstPreservesLiteralSequence(t *testing.T) {
	// An initial empty clause makes UNSAT immediate; identity must still reject
	// reordered or deduplicated literals in another initial clause.
	words := []uint32{Magic, 2, 2, 5, 0, 0, 0, 0, 3, 1, 3, 1, 0}
	for _, formula := range []string{"p cnf 2 2\n1 2 1 0\n0\n", "p cnf 2 2\n2 1 1 0\n0\n", "p cnf 2 2\n1 2 0\n0\n"} {
		_, err := CheckWordsAgainst(formula, words)
		if (err == nil) != (formula == "p cnf 2 2\n1 2 1 0\n0\n") {
			t.Fatalf("%q: %v", formula, err)
		}
	}
}

func TestWordsMatchFormulaDoesNotAcceptProof(t *testing.T) {
	formula := []uint32{Magic, 1, 1, 2, 0, 0, 0, 0, 1, 1}
	if !WordsMatchFormula(formula, formula) {
		t.Fatal("well-framed identity rejected")
	}
	if _, err := CheckWordsAgainst("p cnf 1 1\n1 0\n", formula); err == nil {
		t.Fatal("identity accepted a satisfiable formula")
	}
}
