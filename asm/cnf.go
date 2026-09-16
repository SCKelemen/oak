package asm

// The bit-level obligation as clauses (docs/spec/125-verification.md §3,
// the certificate rung; docs/notes/provers-2026-09.md). The blaster lowers
// a theorem's terms to gates over edges `2*node + c`; the decision-diagram
// engine (asm/bdd.go) canonicalizes them, and this engine writes them as
// Tseitin clauses instead — one fresh variable per distinct gate, the same
// constant folding and structural sharing the diagram gets from its unique
// table — so the same lowering drives both. The obligation clause is "some
// trap fires, or the claim is false": the formula is unsatisfiable exactly
// when the theorem holds, and a model of it is a counterexample read back
// through the parameter bits. The solver that decides it is untrusted; its
// LRAT certificate is checked (internal/lrat/lrat.go through prove's
// compatibility surface, and prove/solver/lrat.oak), and
// the checker, not the solver's verdict, settles the row.

import (
	"fmt"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// cnfClauseBudget bounds the clauses one obligation may take, as the node
// budget bounds a diagram: beyond it the engine reports exhaustion.
const cnfClauseBudget = 50_000_000

// cnfBuilder is the clause engine behind a blaster. An edge is
// `2*variable + c` with variable ≥ 1 a DIMACS variable; edge 0 is false and
// edge 1 true, as in the diagram engine, so `not` is the same bit flip.
type cnfBuilder struct {
	variables int
	clauses   [][]int
	// inputs maps a blaster variable index to its DIMACS variable, allocated
	// on first use so parameter bits and gates share one numbering.
	inputs map[int]int
	memo   map[cnfKey]int
	// gates records every fresh gate in creation order (kind, operands,
	// result) so a model can be evaluated from its inputs alone.
	gates    []cnfGate
	exceeded bool
}

type cnfKey struct{ op, x, y, z int }

type cnfGate struct {
	op      int // opAnd, opOr, opXor, or cnfIte
	x, y, z int // edges; z is the else edge of an ite
	out     int // the gate's variable (positive edge 2*out)
}

const cnfIte = 3

func newCNFBuilder() *cnfBuilder {
	return &cnfBuilder{inputs: map[int]int{}, memo: map[cnfKey]int{}}
}

// lit is the DIMACS literal of a non-constant edge.
func cnfLit(edge int) int {
	if edge&1 == 1 {
		return -(edge >> 1)
	}
	return edge >> 1
}

func (c *cnfBuilder) fresh() int {
	c.variables++
	return c.variables
}

func (c *cnfBuilder) clause(lits ...int) {
	if len(c.clauses) >= cnfClauseBudget {
		c.exceeded = true
		return
	}
	c.clauses = append(c.clauses, lits)
}

// variable is the edge of blaster variable v.
func (c *cnfBuilder) variable(v int) int {
	if dimacs, known := c.inputs[v]; known {
		return 2 * dimacs
	}
	dimacs := c.fresh()
	c.inputs[v] = dimacs
	return 2 * dimacs
}

// apply is the Tseitin gate for x op y, with the constant and
// identity folds the diagram engine performs on terminal shapes.
func (c *cnfBuilder) apply(op, x, y int) int {
	if x > y {
		x, y = y, x
	}
	switch {
	case x == y:
		if op == opXor {
			return bddFalse
		}
		return x
	case x^1 == y:
		if op == opAnd {
			return bddFalse
		}
		return bddTrue
	case x == bddFalse:
		switch op {
		case opAnd:
			return bddFalse
		default: // or, xor
			return y
		}
	case x == bddTrue:
		switch op {
		case opAnd:
			return y
		case opOr:
			return bddTrue
		default:
			return y ^ 1
		}
	}
	key := cnfKey{op, x, y, -1}
	if g, seen := c.memo[key]; seen {
		return 2 * g
	}
	g := c.fresh()
	c.memo[key] = g
	a, b := cnfLit(x), cnfLit(y)
	switch op {
	case opAnd:
		c.clause(-g, a)
		c.clause(-g, b)
		c.clause(g, -a, -b)
	case opOr:
		c.clause(g, -a)
		c.clause(g, -b)
		c.clause(-g, a, b)
	case opXor:
		c.clause(-g, a, b)
		c.clause(-g, -a, -b)
		c.clause(g, -a, b)
		c.clause(g, a, -b)
	}
	c.gates = append(c.gates, cnfGate{op: op, x: x, y: y, out: g})
	return 2 * g
}

// ite is the mux gate cond ? t : e, folded when an operand is constant or
// the arms coincide.
func (c *cnfBuilder) ite(cond, t, e int) int {
	switch {
	case cond == bddTrue:
		return t
	case cond == bddFalse:
		return e
	case t == e:
		return t
	case t == bddTrue && e == bddFalse:
		return cond
	case t == bddFalse && e == bddTrue:
		return cond ^ 1
	case t == bddTrue:
		return c.apply(opOr, cond, e)
	case t == bddFalse:
		return c.apply(opAnd, cond^1, e)
	case e == bddTrue:
		return c.apply(opOr, cond^1, t)
	case e == bddFalse:
		return c.apply(opAnd, cond, t)
	}
	key := cnfKey{cnfIte, cond, t, e}
	if g, seen := c.memo[key]; seen {
		return 2 * g
	}
	g := c.fresh()
	c.memo[key] = g
	s, a, b := cnfLit(cond), cnfLit(t), cnfLit(e)
	c.clause(-g, -s, a)
	c.clause(-g, s, b)
	c.clause(g, -s, -a)
	c.clause(g, s, -b)
	// Redundant but propagation-strengthening: when both arms agree the
	// gate agrees whatever the selector.
	c.clause(-g, a, b)
	c.clause(g, -a, -b)
	c.gates = append(c.gates, cnfGate{op: cnfIte, x: cond, y: t, z: e, out: g})
	return 2 * g
}

// The blaster's gate calls dispatch to whichever engine it carries.

func (bl *blaster) apply(op, x, y int) int {
	if bl.cnf != nil {
		return bl.cnf.apply(op, x, y)
	}
	return bl.bdd.apply(op, x, y)
}

func (bl *blaster) ite(c, t, e int) int {
	if bl.cnf != nil {
		return bl.cnf.ite(c, t, e)
	}
	return bl.bdd.ite(c, t, e)
}

func (bl *blaster) not(a int) int { return a ^ 1 }

func (bl *blaster) variable(v int) int {
	if bl.cnf != nil {
		return bl.cnf.variable(v)
	}
	return bl.bdd.variable(v)
}

func (bl *blaster) exceeded() bool {
	if bl.cnf != nil {
		return bl.cnf.exceeded
	}
	return bl.bdd.exceeded
}

// newCNFBlaster is a blaster over the clause engine under the interleaved
// numbering (the order is immaterial to a solver).
func newCNFBlaster(params []string, widths map[string]int) *blaster {
	bl := newBlaster(params, widths)
	bl.bdd = nil
	bl.cnf = newCNFBuilder()
	return bl
}

// CNF is a theorem's bit-level obligation as clauses: unsatisfiable exactly
// when the theorem holds. A model is a counterexample; Owners maps its
// input variables back to parameter bits.
type CNF struct {
	Variables int
	Clauses   int
	Text      string // DIMACS
	Owners    map[int]VariableOwner
	Names     []string
	// Settled is the decision when no solver is needed: the obligation
	// folded to a constant.
	Settled *Decision
	gates   []cnfGate
	// obligation is the final clause's literals (edges), for evaluation.
	obligation []int
	inputs     map[int]int
	// claim and traps are the lowered terms the clauses encode, for
	// confirming a model on the terms themselves (Confirms).
	claim *term
	traps []*term
}

// ExportCNF lowers a theorem to its obligation clauses. The reason names
// what refused the lowering when the third result is false.
func ExportCNF(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations) (CNF, string, bool) {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return CNF{}, undecided.Message, false
	}
	return exportTermCNF("oak prove: "+sig.Name.Value, lowered.names, lowered.widths, lowered.claim, lowered.traps)
}

// exportTermCNF is the one clause authority shared by theorem and native
// equality certificates. claim is a Boolean-valued term; the emitted formula
// is satisfiable exactly when a trap fires or claim is false, modulo the
// explicitly documented abstraction of select/uninterpreted terms.
func exportTermCNF(label string, names []string, widths map[string]int, claim *term, traps []*term) (CNF, string, bool) {
	bl := newCNFBlaster(names, widths)
	var obligation []int
	trapAlways := false
	for _, trap := range traps {
		if trap == nil {
			return CNF{}, "the obligation exceeded the clause budget or uses an operation beyond the bit level", false
		}
		bits := bl.blast(trap)
		if len(bits) != 1 || bl.exceeded() {
			return CNF{}, "the obligation exceeded the clause budget or uses an operation beyond the bit level", false
		}
		switch bits[0] {
		case bddFalse:
			continue
		case bddTrue:
			trapAlways = true
		default:
			obligation = append(obligation, bits[0])
		}
	}
	if claim == nil {
		return CNF{}, "the obligation exceeded the clause budget or uses an operation beyond the bit level", false
	}
	claimBits := bl.blast(claim)
	if len(claimBits) != 1 || bl.exceeded() {
		return CNF{}, "the obligation exceeded the clause budget or uses an operation beyond the bit level", false
	}
	out := CNF{Owners: map[int]VariableOwner{}, Names: names, gates: bl.cnf.gates, inputs: bl.cnf.inputs, claim: claim, traps: traps}
	for v, dimacs := range bl.cnf.inputs {
		if owner, isParam := bl.owners[v]; isParam {
			out.Owners[dimacs] = VariableOwner{Param: owner.param, Bit: owner.bit}
		}
	}
	switch {
	case trapAlways:
		out.Settled = &Decision{Kind: DecisionRefuted, Message: "the body traps on every input"}
		if err := validateSettledCNFObligation(bl, traps, claim, cnfObligationTrapAlways, obligation); err != nil {
			return CNF{}, fmt.Sprintf("internal CNF obligation check failed: %v", err), false
		}
		return out, "", true
	case claimBits[0] == bddFalse:
		out.Settled = &Decision{Kind: DecisionRefuted, Message: "the claim is false on every input"}
		if err := validateSettledCNFObligation(bl, traps, claim, cnfObligationClaimFalse, obligation); err != nil {
			return CNF{}, fmt.Sprintf("internal CNF obligation check failed: %v", err), false
		}
		return out, "", true
	case claimBits[0] != bddTrue:
		obligation = append(obligation, claimBits[0]^1)
	}
	if len(obligation) == 0 {
		out.Settled = &Decision{Kind: DecisionProven, Message: "at the bit level (the obligation is constant)"}
		if err := validateSettledCNFObligation(bl, traps, claim, cnfObligationConstantProven, obligation); err != nil {
			return CNF{}, fmt.Sprintf("internal CNF obligation check failed: %v", err), false
		}
		return out, "", true
	}
	if err := validateCNFObligation(bl, traps, claim, cnfObligationFormula, obligation); err != nil {
		return CNF{}, fmt.Sprintf("internal CNF obligation check failed: %v", err), false
	}
	final := make([]int, len(obligation))
	for i, edge := range obligation {
		final[i] = cnfLit(edge)
	}
	clauses := append(bl.cnf.clauses, final)
	if err := validateCNFTrace(bl.cnf, obligation, clauses); err != nil {
		return CNF{}, fmt.Sprintf("internal CNF trace check failed: %v", err), false
	}
	out.obligation = obligation
	out.Variables = bl.cnf.variables
	out.Clauses = len(clauses)
	var b strings.Builder
	fmt.Fprintf(&b, "c %s\n", label)
	fmt.Fprintf(&b, "p cnf %d %d\n", out.Variables, out.Clauses)
	for _, clause := range clauses {
		for _, lit := range clause {
			b.WriteString(strconv.Itoa(lit))
			b.WriteByte(' ')
		}
		b.WriteString("0\n")
	}
	out.Text = b.String()
	return out, "", true
}

// Confirms evaluates the lowered claim and traps at a parameter
// assignment and reports whether it is a counterexample on the terms
// themselves: the claim false, or a trap fired. The clauses abstract an
// uninterpreted operation (integer division by a constant that is not a
// power of two, a floating-point operation) as free variables, so a model
// of the clauses may satisfy the claim — division by three is not any
// function of its operands; only an assignment the evaluation confirms
// refutes the theorem.
func (c CNF) Confirms(params map[string]uint64) bool {
	if c.claim == nil {
		return true // a settled obligation has no terms to evaluate
	}
	evaluator := newTermEvaluator(append([]*term{c.claim}, c.traps...)...)
	for _, trap := range c.traps {
		if evaluator.evaluate(trap, params) != 0 {
			return true
		}
	}
	return evaluator.evaluate(c.claim, params) != 1
}

// Counterexample reads a model (positive literals of the input variables)
// back into the parameter assignment it names.
func (c CNF) Counterexample(model []int) string {
	env := map[string]uint64{}
	for _, lit := range model {
		if lit <= 0 {
			continue
		}
		if owner, isInput := c.Owners[lit]; isInput {
			env[owner.Param] |= uint64(1) << uint(owner.Bit)
		}
	}
	return describeEnv(c.Names, env)
}

// Evaluate decides the obligation clause under one parameter assignment by
// running the gates in creation order: true means the assignment is a
// counterexample. Select variables (uninterpreted element reads) are zero.
func (c CNF) Evaluate(params map[string]uint64) bool {
	value := map[int]bool{}
	for dimacs, owner := range c.Owners {
		value[dimacs] = (params[owner.Param]>>uint(owner.Bit))&1 == 1
	}
	edge := func(e int) bool {
		if e == bddFalse {
			return false
		}
		if e == bddTrue {
			return true
		}
		v := value[e>>1]
		if e&1 == 1 {
			return !v
		}
		return v
	}
	for _, g := range c.gates {
		switch g.op {
		case opAnd:
			value[g.out] = edge(g.x) && edge(g.y)
		case opOr:
			value[g.out] = edge(g.x) || edge(g.y)
		case opXor:
			value[g.out] = edge(g.x) != edge(g.y)
		case cnfIte:
			if edge(g.x) {
				value[g.out] = edge(g.y)
			} else {
				value[g.out] = edge(g.z)
			}
		}
	}
	for _, e := range c.obligation {
		if edge(e) {
			return true
		}
	}
	return false
}

// InputBits is the number of parameter bits the obligation reads, for a
// brute-force cross-check to size itself.
func (c CNF) InputBits() int {
	widths := map[string]int{}
	for _, owner := range c.Owners {
		if owner.Bit+1 > widths[owner.Param] {
			widths[owner.Param] = owner.Bit + 1
		}
	}
	total := 0
	names := make([]string, 0, len(widths))
	for name := range widths {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		total += widths[name]
	}
	return total
}

// ModelParams reads a model's positive input literals into the parameter
// assignment they name, for Evaluate to confirm before a counterexample
// is reported.
func (c CNF) ModelParams(model []int) map[string]uint64 {
	env := map[string]uint64{}
	for _, name := range c.Names {
		env[name] = 0
	}
	for _, lit := range model {
		if lit <= 0 {
			continue
		}
		if owner, isInput := c.Owners[lit]; isInput {
			env[owner.Param] |= uint64(1) << uint(owner.Bit)
		}
	}
	return env
}
