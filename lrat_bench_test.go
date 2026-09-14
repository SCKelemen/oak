package main

import (
	"testing"

	"github.com/SCKelemen/oak/prove"
)

// The two LRAT checkers over one certificate the solver written in Oak
// produces (pigeonhole 7 into 6): the Go checker's text pass and the Oak
// checker's word pass, each a linear walk with no allocation per step.
func BenchmarkLRATCheckers(b *testing.B) {
	variables, clauses := pigeonhole(6)
	cnf := cnfOf(variables, clauses)
	outcome, err := runOakSAT(cnf)
	if err != nil || !outcome.Unsatisfiable {
		b.Fatalf("pigeonhole 6: %v %+v", err, outcome)
	}
	b.Run("go", func(b *testing.B) {
		b.SetBytes(int64(len(outcome.Certificate)))
		for i := 0; i < b.N; i++ {
			if _, err := prove.CheckLRAT(cnf.Text, outcome.Certificate); err != nil {
				b.Fatal(err)
			}
		}
	})
	b.Run("oak", func(b *testing.B) {
		b.SetBytes(int64(len(outcome.Certificate)))
		for i := 0; i < b.N; i++ {
			if v, err := runOakLRAT(cnf.Text, outcome.Certificate); err != nil || v.Status != 0 {
				b.Fatalf("%v %+v", err, v)
			}
		}
	})
}
