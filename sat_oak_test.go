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
	// Two contradicting units: found at load, refuted with a certificate.
	units := cnfOf(2, [][]int{{1}, {-1, 2}, {-2}})
	outcome, err = runOakSAT(units)
	if err != nil || !outcome.Unsatisfiable {
		t.Fatalf("contradicting units: want unsatisfiable, got %+v %v", outcome, err)
	}
	checkBoth(t, "contradicting units", units, outcome.Certificate)
	direct := cnfOf(1, [][]int{{1}, {-1}})
	outcome, err = runOakSAT(direct)
	if err != nil || !outcome.Unsatisfiable {
		t.Fatalf("direct contradiction: want unsatisfiable, got %+v %v", outcome, err)
	}
	checkBoth(t, "direct contradiction", direct, outcome.Certificate)
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

// Probing runs before the search: a failed literal is learned as a unit
// with its hints, and a literal implied by both polarities of a variable
// through two recorded implications, deleted once the unit stands. The
// formulas are unsatisfiable so the certificate is kept and checked, and
// the probing steps come first.
func TestOakSATProbing(t *testing.T) {
	// x forces a and b, they force c, and x forbids c; not x forces d
	// and not d. Both polarities fail: the first probe learns a unit of
	// x, whose propagation at level zero closes the derivation.
	variables, failed := padded([][]int{{-1, 2}, {-1, 3}, {-2, -3, 4}, {-1, -4}, {1, 5}, {1, -5}}, 5, 1, 2, 3, 4, 5)
	cnf := cnfOf(variables, failed)
	outcome, err := runOakSAT(cnf)
	if err != nil {
		t.Fatal(err)
	}
	if !outcome.Unsatisfiable {
		t.Fatalf("failed literal: want unsatisfiable, got %+v", outcome)
	}
	steps := certificateSteps(outcome.Certificate)
	if len(steps) != 2 || len(steps[0].literals) != 1 || abs(steps[0].literals[0]) != 1 || len(steps[1].literals) != 0 {
		t.Fatalf("failed literal: want a unit of x then the empty clause, got %+v\n%s", steps, outcome.Certificate)
	}
	checkBoth(t, "failed literal", cnf, outcome.Certificate)
	// u follows from x through a and from not x through b, so u is a
	// unit though neither polarity fails; under u the four sign patterns
	// over p and q are left, which no single propagation reaches.
	variables, both := padded([][]int{{-1, 2}, {1, 3}, {-2, 4}, {-3, 4}, {-4, 5, 6}, {-4, -5, 6}, {-4, 5, -6}, {-4, -5, -6}}, 6, 1, 2, 3, 4, 5, 6)
	cnf = cnfOf(variables, both)
	outcome, err = runOakSAT(cnf)
	if err != nil {
		t.Fatal(err)
	}
	if !outcome.Unsatisfiable {
		t.Fatalf("both polarities: want unsatisfiable, got %+v", outcome)
	}
	steps = certificateSteps(outcome.Certificate)
	if len(steps) < 4 {
		t.Fatalf("both polarities: want two implications, a unit, and more, got %+v\n%s", steps, outcome.Certificate)
	}
	if len(steps[0].literals) != 2 || len(steps[1].literals) != 2 || len(steps[2].literals) != 1 || steps[2].literals[0] != 4 {
		t.Fatalf("both polarities: want x|u and -x|u, then the unit u, got %+v\n%s", steps, outcome.Certificate)
	}
	if len(steps[2].hints) != 2 || steps[2].hints[0] != steps[0].id || steps[2].hints[1] != steps[1].id {
		t.Fatalf("both polarities: the unit's hints must be the two implications, got %+v", steps[2])
	}
	if !strings.Contains(outcome.Certificate, fmt.Sprintf(" d %d %d 0", steps[0].id, steps[1].id)) {
		t.Fatalf("both polarities: the implications are not deleted after the unit\n%s", outcome.Certificate)
	}
	if len(steps[len(steps)-1].literals) != 0 {
		t.Fatalf("both polarities: want the empty clause last, got %+v", steps[len(steps)-1])
	}
	checkBoth(t, "both polarities", cnf, outcome.Certificate)
}

// padded appends, for each listed variable, eleven clauses holding it
// positively beside two of twelve frame variables, and every three-literal
// positive clause over the frame, so bounded variable elimination (at most
// ten occurrences on each side) passes over the listed variables and the
// frame alike. The frame is satisfied by any assignment making it true
// and constrains nothing else.
func padded(clauses [][]int, variables int, protect ...int) (int, [][]int) {
	frame := make([]int, 12)
	for i := range frame {
		frame[i] = variables + 1 + i
	}
	for _, v := range protect {
		for i := 0; i < 11; i++ {
			clauses = append(clauses, []int{v, frame[i], frame[i+1]})
		}
	}
	for i := 0; i < 12; i++ {
		for j := i + 1; j < 12; j++ {
			for k := j + 1; k < 12; k++ {
				clauses = append(clauses, []int{frame[i], frame[j], frame[k]})
			}
		}
	}
	return variables + 12, clauses
}

type certificateStep struct {
	id       int
	literals []int
	hints    []int
}

// certificateSteps reads the addition lines of an LRAT text.
func certificateSteps(text string) []certificateStep {
	var steps []certificateStep
	for _, line := range strings.Split(text, "\n") {
		fields := strings.Fields(line)
		if len(fields) < 3 || fields[1] == "d" {
			continue
		}
		var step certificateStep
		fmt.Sscan(fields[0], &step.id)
		i := 1
		for ; i < len(fields) && fields[i] != "0"; i++ {
			var l int
			fmt.Sscan(fields[i], &l)
			step.literals = append(step.literals, l)
		}
		for i++; i < len(fields) && fields[i] != "0"; i++ {
			var h int
			fmt.Sscan(fields[i], &h)
			step.hints = append(step.hints, h)
		}
		steps = append(steps, step)
	}
	return steps
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
