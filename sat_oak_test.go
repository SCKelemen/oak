package main

import (
	"fmt"
	"math/rand"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/prove"
)

// cnfOf builds an asm.CNF from clauses over `variables` DIMACS variables,
// with an evaluator over full assignments for the brute-force check.
func cnfOf(variables int, clauses [][]int) asm.CNF {
	var b strings.Builder
	fmt.Fprintf(&b, "p cnf %d %d\n", variables, len(clauses))
	for _, c := range clauses {
		for _, l := range c {
			fmt.Fprintf(&b, "%d ", l)
		}
		b.WriteString("0\n")
	}
	return asm.CNF{Variables: variables, Clauses: len(clauses), Text: b.String()}
}

func satisfies(clauses [][]int, model []int) bool {
	value := map[int]bool{}
	for _, l := range model {
		if l > 0 {
			value[l] = true
		} else {
			value[-l] = false
		}
	}
	for _, c := range clauses {
		ok := false
		for _, l := range c {
			v, set := value[abs(l)]
			if set && v == (l > 0) {
				ok = true
				break
			}
		}
		if !ok {
			return false
		}
	}
	return true
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// bruteForce decides satisfiability over every assignment (small only).
func bruteForce(variables int, clauses [][]int) bool {
	for bits := 0; bits < 1<<uint(variables); bits++ {
		model := make([]int, variables)
		for v := 1; v <= variables; v++ {
			if bits>>uint(v-1)&1 == 1 {
				model[v-1] = v
			} else {
				model[v-1] = -v
			}
		}
		if satisfies(clauses, model) {
			return true
		}
	}
	return false
}

// checkBoth requires the certificate accepted by the Go checker and the
// checker written in Oak.
func checkBoth(t *testing.T, name string, cnf asm.CNF, certificate string) {
	if _, err := prove.CheckLRAT(cnf.Text, certificate); err != nil {
		t.Fatalf("%s: the Go checker refused the certificate: %v\n%s", name, err, certificate)
	}
	oak, err := runOakLRAT(cnf.Text, certificate)
	if err != nil {
		t.Fatalf("%s: %v", name, err)
	}
	if oak.Status != 0 {
		t.Fatalf("%s: the Oak checker refused the certificate (status %d)\n%s", name, oak.Status, certificate)
	}
}

// pigeonhole is the unsatisfiable formula placing n+1 pigeons in n holes:
// every pigeon has a hole, no hole has two pigeons. It needs learning.
func pigeonhole(n int) (int, [][]int) {
	pigeons := n + 1
	variable := func(p, h int) int { return p*n + h + 1 }
	var clauses [][]int
	for p := 0; p < pigeons; p++ {
		var c []int
		for h := 0; h < n; h++ {
			c = append(c, variable(p, h))
		}
		clauses = append(clauses, c)
	}
	for h := 0; h < n; h++ {
		for p := 0; p < pigeons; p++ {
			for q := p + 1; q < pigeons; q++ {
				clauses = append(clauses, []int{-variable(p, h), -variable(q, h)})
			}
		}
	}
	return pigeons * n, clauses
}

func TestOakSATFixtures(t *testing.T) {
	// The four sign patterns over two variables: unsatisfiable.
	unsat := cnfOf(2, [][]int{{1, 2}, {-1, 2}, {1, -2}, {-1, -2}})
	outcome, err := runOakSAT(unsat)
	if err != nil {
		t.Fatal(err)
	}
	if !outcome.Unsatisfiable {
		t.Fatalf("four sign patterns: want unsatisfiable, got %+v", outcome)
	}
	checkBoth(t, "four sign patterns", unsat, outcome.Certificate)
	// A satisfiable chain.
	sat := cnfOf(3, [][]int{{1, 2}, {-1, 3}, {-2, -3}, {2, 3}})
	outcome, err = runOakSAT(sat)
	if err != nil {
		t.Fatal(err)
	}
	if !outcome.Satisfiable || !satisfies([][]int{{1, 2}, {-1, 3}, {-2, -3}, {2, 3}}, outcome.Model) {
		t.Fatalf("chain: want a satisfying model, got %+v", outcome)
	}
	// An empty clause in the formula.
	empty := cnfOf(1, [][]int{{}})
	outcome, err = runOakSAT(empty)
	if err != nil || !outcome.Unsatisfiable {
		t.Fatalf("empty clause: want unsatisfiable, got %+v %v", outcome, err)
	}
	checkBoth(t, "empty clause", empty, outcome.Certificate)
	// Pigeonhole 4 into 3 and 7 into 6; the second learns past the
	// reduction limit and its certificate carries a deletion line.
	for _, n := range []int{3, 6} {
		variables, clauses := pigeonhole(n)
		cnf := cnfOf(variables, clauses)
		outcome, err := runOakSAT(cnf)
		if err != nil {
			t.Fatal(err)
		}
		if !outcome.Unsatisfiable {
			t.Fatalf("pigeonhole %d: want unsatisfiable, got %+v", n, outcome)
		}
		checkBoth(t, fmt.Sprintf("pigeonhole %d", n), cnf, outcome.Certificate)
		if n == 6 && !strings.Contains(outcome.Certificate, " d ") {
			t.Fatalf("pigeonhole %d: the run learned enough to reduce, but the certificate has no deletion line", n)
		}
	}
}

// Random 3-SAT near the threshold, against brute force: the verdict agrees,
// a model satisfies the clauses, a certificate passes both checkers.
func TestOakSATAgainstBruteForce(t *testing.T) {
	rng := rand.New(rand.NewSource(20260913))
	variables := 12
	for seed := 0; seed < 24; seed++ {
		count := 40 + rng.Intn(25)
		clauses := make([][]int, count)
		for i := range clauses {
			c := make([]int, 3)
			for j := range c {
				c[j] = rng.Intn(variables) + 1
				if rng.Intn(2) == 0 {
					c[j] = -c[j]
				}
			}
			clauses[i] = c
		}
		cnf := cnfOf(variables, clauses)
		outcome, err := runOakSAT(cnf)
		if err != nil {
			t.Fatalf("instance %d: %v", seed, err)
		}
		want := bruteForce(variables, clauses)
		if outcome.Satisfiable != want {
			t.Fatalf("instance %d: solver says satisfiable=%v, brute force %v", seed, outcome.Satisfiable, want)
		}
		if outcome.Satisfiable {
			if !satisfies(clauses, outcome.Model) {
				t.Fatalf("instance %d: the model does not satisfy the clauses", seed)
			}
		} else {
			checkBoth(t, fmt.Sprintf("instance %d", seed), cnf, outcome.Certificate)
		}
	}
}
