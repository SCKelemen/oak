package asm

import (
	"reflect"
	"strings"
	"testing"
)

// The clause engine's gates against the truth tables (Oak.Tseitin): for
// each gate kind, the emitted clauses hold under an assignment exactly when
// the gate variable equals the operation's value, and the folds return the
// operand or constant the laws name instead of a gate.
func TestCNFGatesMatchTruthTables(t *testing.T) {
	holds := func(clauses [][]int, value map[int]bool) bool {
		for _, clause := range clauses {
			satisfied := false
			for _, lit := range clause {
				v := value[lit]
				if lit < 0 {
					v = !value[-lit]
				}
				if v {
					satisfied = true
					break
				}
			}
			if !satisfied {
				return false
			}
		}
		return true
	}
	type binary struct {
		op   int
		name string
		fn   func(a, b bool) bool
	}
	for _, gate := range []binary{
		{opAnd, "and", func(a, b bool) bool { return a && b }},
		{opOr, "or", func(a, b bool) bool { return a || b }},
		{opXor, "xor", func(a, b bool) bool { return a != b }},
	} {
		c := newCNFBuilder()
		x, y := c.variable(0), c.variable(1)
		g := c.apply(gate.op, x, y)
		if g&1 != 0 || g>>1 <= 2 {
			t.Fatalf("%s: expected a fresh positive gate edge, got %d", gate.name, g)
		}
		for bits := 0; bits < 8; bits++ {
			value := map[int]bool{1: bits&1 == 1, 2: bits&2 == 2, g >> 1: bits&4 == 4}
			want := value[g>>1] == gate.fn(value[1], value[2])
			if got := holds(c.clauses, value); got != want {
				t.Errorf("%s: x=%v y=%v g=%v: clauses hold %v, law says %v", gate.name, value[1], value[2], value[g>>1], got, want)
			}
		}
	}
	c := newCNFBuilder()
	cond, th, el := c.variable(0), c.variable(1), c.variable(2)
	g := c.ite(cond, th, el)
	for bits := 0; bits < 16; bits++ {
		value := map[int]bool{1: bits&1 == 1, 2: bits&2 == 2, 3: bits&4 == 4, g >> 1: bits&8 == 8}
		expected := value[3]
		if value[1] {
			expected = value[2]
		}
		want := value[g>>1] == expected
		if got := holds(c.clauses, value); got != want {
			t.Errorf("ite: c=%v t=%v e=%v g=%v: clauses hold %v, law says %v", value[1], value[2], value[3], value[g>>1], got, want)
		}
	}
}

func TestCNFFoldsAreTheLaws(t *testing.T) {
	c := newCNFBuilder()
	x, y := c.variable(0), c.variable(1)
	cases := []struct {
		name string
		got  int
		want int
	}{
		{"x and x = x", c.apply(opAnd, x, x), x},
		{"x or x = x", c.apply(opOr, x, x), x},
		{"x xor x = false", c.apply(opXor, x, x), bddFalse},
		{"x and not x = false", c.apply(opAnd, x, x^1), bddFalse},
		{"x or not x = true", c.apply(opOr, x, x^1), bddTrue},
		{"x xor not x = true", c.apply(opXor, x, x^1), bddTrue},
		{"false and y = false", c.apply(opAnd, bddFalse, y), bddFalse},
		{"true and y = y", c.apply(opAnd, bddTrue, y), y},
		{"false or y = y", c.apply(opOr, bddFalse, y), y},
		{"true or y = true", c.apply(opOr, bddTrue, y), bddTrue},
		{"false xor y = y", c.apply(opXor, bddFalse, y), y},
		{"true xor y = not y", c.apply(opXor, bddTrue, y), y ^ 1},
		{"ite true t e = t", c.ite(bddTrue, x, y), x},
		{"ite false t e = e", c.ite(bddFalse, x, y), y},
		{"ite c t t = t", c.ite(x, y, y), y},
		{"ite c true false = c", c.ite(x, bddTrue, bddFalse), x},
		{"ite c false true = not c", c.ite(x, bddFalse, bddTrue), x ^ 1},
	}
	for _, k := range cases {
		if k.got != k.want {
			t.Errorf("%s: got edge %d, want %d", k.name, k.got, k.want)
		}
	}
	if len(c.clauses) != 0 {
		t.Errorf("the folds emitted %d clauses; a fold emits none", len(c.clauses))
	}
	// The arm folds into a gate of the other kind.
	before := len(c.clauses)
	if g := c.ite(x, bddTrue, y); g != c.apply(opOr, x, y) {
		t.Errorf("ite c true e = c or e: got %d, want %d", g, c.apply(opOr, x, y))
	}
	if len(c.clauses) != before+3 {
		t.Errorf("one or-gate emits three clauses, got %d", len(c.clauses)-before)
	}
}

// Pin the signed-literal convention and the raw fresh-gate clause order used
// by Oak.TseitinCNF. Semantic truth-table tests alone would not detect a drift
// in this concrete representation at the RUP boundary.
func TestCNFGateClausesMatchLeanBridge(t *testing.T) {
	for edge, want := range map[int]int{
		2: 1,
		3: -1,
		4: 2,
		5: -2,
	} {
		if got := cnfLit(edge); got != want {
			t.Errorf("cnfLit(%d) = %d, want %d", edge, got, want)
		}
	}

	type gateCase struct {
		name  string
		build func(*cnfBuilder) int
		want  [][]int
	}
	cases := []gateCase{
		{
			name: "and with complemented left operand",
			build: func(c *cnfBuilder) int {
				left, right := c.variable(0)^1, c.variable(1)
				return c.apply(opAnd, left, right)
			},
			want: [][]int{{-3, -1}, {-3, 2}, {3, 1, -2}},
		},
		{
			name: "or with complemented left operand",
			build: func(c *cnfBuilder) int {
				left, right := c.variable(0)^1, c.variable(1)
				return c.apply(opOr, left, right)
			},
			want: [][]int{{3, 1}, {3, -2}, {-3, -1, 2}},
		},
		{
			name: "xor with complemented left operand",
			build: func(c *cnfBuilder) int {
				left, right := c.variable(0)^1, c.variable(1)
				return c.apply(opXor, left, right)
			},
			want: [][]int{{-3, -1, 2}, {-3, 1, -2}, {3, 1, 2}, {3, -1, -2}},
		},
		{
			name: "ite with complemented condition and else operand",
			build: func(c *cnfBuilder) int {
				condition := c.variable(0) ^ 1
				thenValue := c.variable(1)
				elseValue := c.variable(2) ^ 1
				return c.ite(condition, thenValue, elseValue)
			},
			want: [][]int{
				{-4, 1, 2},
				{-4, -1, -3},
				{4, 1, -2},
				{4, -1, 3},
				{-4, 2, -3},
				{4, -2, 3},
			},
		},
	}

	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			builder := newCNFBuilder()
			gate := test.build(builder)
			wantGate := 2 * (len(builder.inputs) + 1)
			if gate != wantGate {
				t.Fatalf("gate edge = %d, want fresh positive edge %d", gate, wantGate)
			}
			if !reflect.DeepEqual(builder.clauses, test.want) {
				t.Fatalf("clauses = %v, want %v", builder.clauses, test.want)
			}
		})
	}
}

func TestExportTermCNFSettlesFalseClaimWithSymbolicTrap(t *testing.T) {
	trap := paramTerm("trap", 1)
	cnf, reason, ok := exportTermCNF(
		"false claim with symbolic trap",
		[]string{"trap"},
		map[string]int{"trap": 1},
		constTerm(0, 1),
		[]*term{trap},
	)
	if !ok || reason != "" {
		t.Fatalf("export refused: ok=%v reason=%q", ok, reason)
	}
	if cnf.Settled == nil || cnf.Settled.Kind != DecisionRefuted {
		t.Fatalf("settled = %#v, want constant refutation", cnf.Settled)
	}
	if cnf.Text != "" || cnf.Clauses != 0 {
		t.Fatalf("constant obligation emitted DIMACS: clauses=%d text=%q", cnf.Clauses, cnf.Text)
	}
}

// The matching Oak.TseitinCNF.SequenceExample has an AND whose output feeds a
// XOR. Pin the mutable builder's creation order, canonical operand order, and
// gate-clause portion against that exact example.
func TestCNFSequentialGateClausesMatchLeanBridge(t *testing.T) {
	builder := newCNFBuilder()
	input1, input2 := builder.variable(0), builder.variable(1)
	and := builder.apply(opAnd, input1, input2)
	xor := builder.apply(opXor, and, input1^1)

	if and != 6 || xor != 8 {
		t.Fatalf("gate edges = (%d, %d), want (6, 8)", and, xor)
	}
	wantGates := []cnfGate{
		{op: opAnd, x: 2, y: 4, out: 3},
		{op: opXor, x: 3, y: 6, out: 4},
	}
	if !reflect.DeepEqual(builder.gates, wantGates) {
		t.Fatalf("gates = %#v, want %#v", builder.gates, wantGates)
	}
	wantClauses := [][]int{
		{-3, 1},
		{-3, 2},
		{3, -1, -2},
		{-4, -1, 3},
		{-4, 1, -3},
		{4, 1, 3},
		{4, -1, -3},
	}
	if !reflect.DeepEqual(builder.clauses, wantClauses) {
		t.Fatalf("clauses = %v, want %v", builder.clauses, wantClauses)
	}
}

// The nonconstant final obligation is traps in supplied order followed by the
// negated claim. No Boolean constant may reach cnfLit: zero is DIMACS syntax,
// not a literal.
func TestExportTermCNFFinalClauseOrderAndPolarity(t *testing.T) {
	trap1 := paramTerm("trap1", 1)
	trap2 := paramTerm("trap2", 1)
	claim := paramTerm("claim", 1)
	cnf, reason, ok := exportTermCNF(
		"symbolic final obligation",
		[]string{"trap1", "trap2", "claim"},
		map[string]int{"trap1": 1, "trap2": 1, "claim": 1},
		claim,
		[]*term{trap1, trap2},
	)
	if !ok || reason != "" || cnf.Settled != nil {
		t.Fatalf("export = ok %v reason %q settled %#v", ok, reason, cnf.Settled)
	}
	if !reflect.DeepEqual(cnf.obligation, []int{2, 4, 7}) {
		t.Fatalf("obligation edges = %v, want [2 4 7]", cnf.obligation)
	}
	want := "c symbolic final obligation\np cnf 3 1\n1 2 -3 0\n"
	if cnf.Text != want {
		t.Fatalf("DIMACS = %q, want %q", cnf.Text, want)
	}
	lines := strings.Split(strings.TrimSpace(cnf.Text), "\n")
	fields := strings.Fields(lines[len(lines)-1])
	if len(fields) == 0 || fields[len(fields)-1] != "0" {
		t.Fatalf("final clause has no DIMACS terminator: %v", fields)
	}
	for _, field := range fields[:len(fields)-1] {
		if field == "0" {
			t.Fatal("the final clause contains a constant/terminator literal")
		}
	}
}
