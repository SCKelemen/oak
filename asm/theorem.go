package asm

import (
	"fmt"
	"sort"
	"sync/atomic"

	"github.com/SCKelemen/oak/ast"
)

// The bit-level theorem decider (docs/spec/125-verification.md §3). A
// theorem over fixed-width scalar parameters is a Bool-valued Oak body; the
// verifier already lowers such bodies to its term language (the semantics of
// Oak.AssemblerSemantics, checked against the silicon) and decides bit-level
// equalities by bit-blasting. Deciding a theorem is deciding that its body's
// bit is the constant true: the same lowering, the same blaster, the same
// witness inputs first, and a differing bit read back as a counterexample.

// DecisionKind is the decider's verdict.
type DecisionKind int

const (
	// DecisionProven: the body is true for every assignment of its parameters.
	DecisionProven DecisionKind = iota
	// DecisionRefuted: an assignment makes the body false; Message names it.
	DecisionRefuted
	// DecisionUndecided: the body is outside the lowered subset or the
	// blaster's budget; Message says which.
	DecisionUndecided
)

// Decision is the decider's answer about one theorem.
type Decision struct {
	Kind    DecisionKind
	Message string
	// Order names the variable order that proved the theorem at the bit
	// level (interleaved, blocks, control) and Nodes the diagram's size, so
	// the decision can be replayed by the Oak solver (ExportProblem).
	Order string
	Nodes int
}

// loweredTheorem is a theorem in the decider's term language: the claim
// under its hypotheses, the trap obligations, and the parameters with
// their widths.
type loweredTheorem struct {
	claim  *term
	traps  []*term
	names  []string
	widths map[string]int
}

// assembleTheoremRoots projects a lowered body and its raw trap conditions
// into the roots consumed by the deciders and exporters. The aggregate-tag
// hypothesis guards both sides of the obligation. Raw traps retain their
// supplied lowering-encounter order and multiplicity in a fresh slice.
func assembleTheoremRoots(assume, body *term, rawTraps []*term) (*term, []*term) {
	claim := truncate(body, 1)
	hasAssumption := assume.kind != termConst || assume.value != 1
	if hasAssumption {
		claim = binaryTerm("or", binaryTerm("xor", assume, constTerm(1, 1)), claim)
	}
	traps := make([]*term, 0, len(rawTraps))
	for _, trap := range rawTraps {
		trap = truncate(trap, 1)
		if hasAssumption {
			trap = binaryTerm("and", assume, trap)
		}
		traps = append(traps, trap)
	}
	return claim, traps
}

// Guard is a refinement's construction as the decider sees it
// (docs/spec/20-types.md section 12): the value at its base type, and a
// trap obligation that the predicate — a Bool over `value` — holds.
type Guard struct {
	Base      ast.Expression
	Predicate ast.Expression
}

// Declarations are the program's record and sum-type declarations, so a
// theorem may take and pass record and sum-type values: a parameter of
// such a type is bound as an aggregate of scalar leaves — one symbolic
// parameter per field, a tag per union — under the hypothesis that every
// tag names a variant.
type Declarations struct {
	Records map[string]*ast.RecordLiteral
	ADTs    map[string]*ast.ADTType
	// Constants are the program's folded scalar constants, by name. A
	// theorem that names one reads its value, as a body lowered for the
	// native backend does: without them the decider met an identifier
	// that is not a parameter and left the theorem open, so a property
	// stated over a named constant had to be restated over its literal.
	Constants map[string]Constant
}

// DecideTheoremWith is DecideTheorem over a program whose refinements are
// given as guards, keyed by the refinement's name — a construction in the
// body is its argument, with the predicate recorded as a trap condition
// the decider must prove impossible — and whose record and sum-type
// declarations let aggregate parameters, arguments, and results through.
func DecideTheoremWith(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations) Decision {
	return decideTheorem(sig, functions, guards, decls)
}

// DecideTheorem decides a theorem declaration: every parameter a
// fixed-width scalar or Bool, the body in the verifier's subset (wrapping
// arithmetic, bitwise operators, comparisons, conditionals, typed locals,
// counted loops, calls to program functions in the same subset — given in
// functions — inlined; no views or data-dependent loops).
func DecideTheorem(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) Decision {
	return decideTheorem(sig, functions, nil, Declarations{})
}

func decideTheorem(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations) Decision {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return *undecided
	}
	return decideLowered(lowered)
}

// lowerTheorem lowers a theorem to the decider's terms, or says why it
// cannot be decided at the bit level.
func lowerTheorem(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations) (*loweredTheorem, *Decision) {
	undecided := func(message string) (*loweredTheorem, *Decision) {
		return nil, &Decision{Kind: DecisionUndecided, Message: message}
	}
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return undecided("no body")
	}
	lowering := newLowering(sig)
	lowering.functions = functions
	lowering.guards = guards
	lowering.records, lowering.adts = decls.Records, decls.ADTs
	lowering.constants = decls.Constants
	lowering.trapsTracked = true
	for _, param := range sig.Parameters {
		if _, _, ok := contractBits(param.Type); ok {
			continue
		}
		if typ, ok := lowering.oakTypeOf(param.Type); ok && typ.kind != oakScalar {
			continue // bound below as an aggregate of leaves
		}
		return undecided(fmt.Sprintf("parameter %s: %s is not a fixed-width scalar, record, or sum type", param.Name.Value, typeText(param.Type)))
	}
	lowering.bindAggregateParams(sig)
	// Every union tag among the parameters names a variant: the hypothesis
	// under which the body is decided (a tag outside the declaration is
	// not a value of the type).
	assume := constTerm(1, 1)
	for _, param := range sig.Parameters {
		if local, isLocal := lowering.locals[param.Name.Value]; isLocal && local.agg != nil {
			assume = binaryTerm("and", assume, tagsNameVariants(local.agg))
		}
	}
	body := sig.Body
	if loop, isTail := tailRecursionAsLoop(sig, body); isTail {
		body = loop
	}
	t, reason, ok := lowering.lower(body, 1)
	if !ok {
		return undecided(fmt.Sprintf("the body contains %s", reason))
	}
	if len(lowering.loops) > 0 {
		return undecided("the body has a data-dependent loop")
	}
	// Unsigned division is an uninterpreted function of its operands, so
	// a theorem over `/` or `%` had nothing to reason from and the
	// decider reported that its counterexample falsifies only the
	// abstraction. Its defining bound is a fact, so assuming it is sound:
	// where the divisor is not zero the remainder is below it, and the
	// quotient is no greater than the dividend. That decides the range
	// claims — a cursor stepped modulo a catalog's length stays inside it
	// — without blasting a division. A power-of-two divisor folds to a
	// mask before reaching here and needs none of this.
	assume = binaryTerm("and", assume, unsignedDivisionFacts(append([]*term{t}, lowering.traps...)))
	// Under the tag hypothesis: the claim holds, and no trap fires.
	t, traps := assembleTheoremRoots(assume, t, lowering.traps)

	mentioned := map[string]bool{}
	collectParams(t, mentioned)
	for _, trap := range traps {
		collectParams(trap, mentioned)
	}
	names := make([]string, 0, len(mentioned))
	widths := map[string]int{}
	for name := range mentioned {
		names = append(names, name)
		widths[name] = lowering.declaredWidth(name)
	}
	sort.Strings(names)
	return &loweredTheorem{claim: t, traps: traps, names: names, widths: widths}, nil
}

// unsignedDivisionFacts conjoins, for every unsigned division in the
// terms, what its operands make true of its value: with a non-zero
// divisor b and dividend a, the remainder `a - q·b` is below b and the
// quotient q is at most a. Both hold of real division, so assuming them
// cannot make a false claim decide; they are what a range claim over `%`
// needs. Signed division is left alone: its rounding toward zero makes
// the corresponding facts depend on the operands' signs.
func unsignedDivisionFacts(roots []*term) *term {
	facts := constTerm(1, 1)
	seen := map[*term]bool{}
	var walk func(*term)
	walk = func(t *term) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		if t.kind == termFloat && (t.op == "udiv" || t.op == "rv.udiv") && t.left != nil && t.right != nil && t.cond == nil {
			a, b, w := t.left, t.right, t.width
			zero := constTerm(0, w)
			remainder := binaryTerm("sub", a, binaryTerm("mul", t, b))
			divides := binaryTerm("or", cmpTerm("eq", b, zero), cmpTerm("lo", remainder, b))
			bounded := binaryTerm("or", cmpTerm("eq", b, zero), cmpTerm("ls", t, a))
			facts = binaryTerm("and", facts, binaryTerm("and", truncate(divides, 1), truncate(bounded, 1)))
		}
		walk(t.left)
		walk(t.right)
		walk(t.cond)
	}
	for _, root := range roots {
		walk(root)
	}
	return truncate(facts, 1)
}

// decideLowered settles the lowered theorem: the witness inputs first, then
// the diagrams under every variable order at once.
func decideLowered(lowered *loweredTheorem) Decision {
	t, traps, names := lowered.claim, lowered.traps, lowered.names
	if refuted, isRefuted := lowered.witnessRefutation(); isRefuted {
		return refuted
	}
	// The variable orders run together over the same terms, and the first
	// to decide within the node budget stops the others: a proof does not
	// depend on the order, and a theorem that is small under some order is
	// decided in that order's time rather than after the others' failures.
	blasters := lowered.blasters()
	var stop atomic.Bool
	type attempt struct {
		decision Decision
		exceeded bool
	}
	results := make(chan attempt, len(blasters))
	// Number the shared term DAG once before the variable-order attempts run.
	// Each attempt gets private value/stamp storage without writing term ids.
	evaluator := newTermEvaluator(append([]*term{t}, traps...)...)
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		go func(bl *blaster, evaluator *termEvaluator) {
			decision, exceeded := decideBlasted(bl, traps, t, names, evaluator)
			results <- attempt{decision, exceeded}
		}(bl, evaluator.fork())
	}
	for range blasters {
		if a := <-results; !a.exceeded {
			stop.Store(true)
			return a.decision
		}
	}
	return Decision{Kind: DecisionUndecided, Message: "the bit-level decision exceeded its node budget"}
}

// witnessRefutation evaluates the lowered theorem on the fixed witness
// inputs first: a trapping or false case is a counterexample regardless
// of what the canonical form would say.
func (lowered *loweredTheorem) witnessRefutation() (Decision, bool) {
	t, traps, names, widths := lowered.claim, lowered.traps, lowered.names, lowered.widths
	evaluator := newTermEvaluator(append([]*term{t}, traps...)...)
	for _, env := range witnessInputs(names, widths) {
		for _, trap := range traps {
			if evaluator.evaluate(trap, env) != 0 {
				return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count at the width, a failed assert, or a construction outside its predicate) at " + describeEnv(names, env)}, true
			}
		}
		if evaluator.evaluate(t, env) != 1 {
			return Decision{Kind: DecisionRefuted, Message: "counterexample " + describeEnv(names, env)}, true
		}
	}
	return Decision{}, false
}

// blasters builds the variable orders that apply to the lowered theorem:
// interleaved always, per-parameter blocks when there is more than one
// root parameter, control bits first when the control set is proper.
func (lowered *loweredTheorem) blasters() []*blaster {
	t, traps, names, widths := lowered.claim, lowered.traps, lowered.names, lowered.widths
	control := controlParams(append([]*term{t}, traps...))
	blasters := []*blaster{newBlaster(names, widths)}
	if paramGroups(names) > 1 {
		blasters = append(blasters, newGroupedBlaster(names, widths))
	}
	if len(control) > 0 && len(control) < len(names) {
		blasters = append(blasters, newControlFirstBlaster(names, widths, control))
	}
	return blasters
}

// DecideWithOrder decides the theorem under one named variable order
// (interleaved, blocks, control), with no witness pass: the Go decider as
// the cross-check of the Oak solver, whose node count it must match.
func DecideWithOrder(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations, order string) Decision {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return *undecided
	}
	for _, bl := range lowered.blasters() {
		if orderNames[bl.label] != order {
			continue
		}
		evaluator := newTermEvaluator(append([]*term{lowered.claim}, lowered.traps...)...)
		decision, exceeded := decideBlasted(bl, lowered.traps, lowered.claim, lowered.names, evaluator)
		if exceeded {
			return Decision{Kind: DecisionUndecided, Message: "the bit-level decision exceeded its node budget under the " + order + " order"}
		}
		return decision
	}
	return Decision{Kind: DecisionUndecided, Message: "no " + order + " order applies to the theorem"}
}

// WitnessRefutation runs only the witness pass of the decider: a
// counterexample among the fixed inputs, or nothing (the theorem may still
// be false), with the reason when the theorem cannot be lowered.
func WitnessRefutation(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, guards map[string]Guard, decls Declarations) (Decision, bool) {
	lowered, undecided := lowerTheorem(sig, functions, guards, decls)
	if undecided != nil {
		return *undecided, true
	}
	return lowered.witnessRefutation()
}

// controlParams names the parameters the terms read as control: those
// under the condition of a conditional (a selector compared to a constant,
// a guard) or the count of a shift. The rest are data, which flow into
// results and comparisons of results without choosing a branch.
func controlParams(terms []*term) map[string]bool {
	control := map[string]bool{}
	visited := map[*term]bool{}
	// One visited set for every collection: the parameters of a subterm
	// already collected are in control, so a second walk of it adds nothing.
	collected := map[*term]bool{}
	var walk func(t *term)
	walk = func(t *term) {
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		switch t.kind {
		case termIte:
			collectParamsVisited(t.cond, control, collected)
			walk(t.left)
			walk(t.right)
			return
		case termBinary:
			switch t.op {
			case "shl", "shr", "lsr", "asr", "sar", "ror":
				collectParamsVisited(t.right, control, collected)
			}
		}
		walk(t.cond)
		walk(t.left)
		walk(t.right)
	}
	for _, t := range terms {
		walk(t)
	}
	return control
}

// selectorParams names the parameters a conditional's condition reads
// directly: through the conditions of conditionals nested in it, never
// through their arms. In `l == 0 ? cand[0] : l == 1 ? cand[1] : ... != 0`
// the index l is the selector and the elements are the data the
// condition tests; controlParams counts both as control.
func selectorParams(terms []*term) map[string]bool {
	selectors := map[string]bool{}
	visited := map[*term]bool{}
	inCondition := map[*term]bool{}
	var condition func(t *term)
	condition = func(t *term) {
		if t == nil || inCondition[t] {
			return
		}
		inCondition[t] = true
		switch t.kind {
		case termParam:
			selectors[t.name] = true
		case termIte:
			condition(t.cond) // the arms are the data selected
		default:
			condition(t.cond)
			condition(t.left)
			condition(t.right)
		}
	}
	var walk func(t *term)
	walk = func(t *term) {
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		if t.kind == termIte {
			condition(t.cond)
		}
		walk(t.cond)
		walk(t.left)
		walk(t.right)
	}
	for _, t := range terms {
		walk(t)
	}
	return selectors
}

// decideBlasted settles the theorem with one blaster: every recorded trap
// condition must be impossible and the claim must be the true node. The
// second result reports a blown node budget, which the caller may answer
// with another variable order.
func decideBlasted(bl *blaster, traps []*term, t *term, names []string, evaluator *termEvaluator) (Decision, bool) {
	// A refutation is the assignment the diagrams found, evaluated on the
	// terms themselves: the diagrams abstract an uninterpreted operation
	// (integer division by a constant that is not a power of two, a
	// floating-point operation) as a fresh block, so an assignment that
	// falsifies the abstraction may satisfy the claim — division by three
	// is not any function of its operands. Only an assignment the
	// evaluation confirms is a counterexample; otherwise the claim stays
	// undecided at the bit level (open for Lean, as before).
	for _, trap := range traps {
		bits := bl.blast(trap)
		if bits == nil || bl.exceeded() {
			return Decision{}, true
		}
		if bits[0] != bddFalse {
			env := bl.counterexample(bits[0], bddFalse)
			if evaluator.evaluate(trap, env) == 0 {
				return Decision{Kind: DecisionUndecided, Message: "the diagrams fire a trap only under the abstraction of an uninterpreted operation; the body does not trap at the assignment they chose"}, false
			}
			return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count at the width, a failed assert, or a construction outside its predicate) at " + describeEnv(names, env)}, false
		}
	}
	bits := bl.blast(t)
	if bits == nil || bl.exceeded() {
		return Decision{}, true
	}
	if bits[0] == bddTrue {
		order := ""
		if bl.grouped {
			order = ", " + bl.label
		}
		return Decision{Kind: DecisionProven, Message: fmt.Sprintf("at the bit level (%d BDD nodes%s)", len(bl.bdd.nodes), order), Order: orderNames[bl.label], Nodes: len(bl.bdd.nodes)}, false
	}
	env := bl.counterexample(bits[0], bddTrue)
	if evaluator.evaluate(t, env) == 1 {
		return Decision{Kind: DecisionUndecided, Message: "the diagrams differ only under the abstraction of an uninterpreted operation; the claim holds at the assignment they chose"}, false
	}
	return Decision{Kind: DecisionRefuted, Message: "counterexample " + describeEnv(names, env)}, false
}

// tagsNameVariants is the 1-bit term stating that every union tag inside
// an aggregate parameter is one of its declared variants' tags.
func tagsNameVariants(v *oakValue) *term {
	valid := constTerm(1, 1)
	if v == nil || v.typ == nil {
		return valid
	}
	switch v.typ.kind {
	case oakADT:
		tag := v.fields["tag"].scalar
		names := constTerm(0, 1)
		for _, variant := range v.typ.variants {
			names = binaryTerm("or", names, truncate(cmpTerm("eq", tag, constTerm(uint64(variant.tag), 32)), 1))
			if variant.payload != nil {
				if payload, has := v.fields[variant.name]; has {
					valid = binaryTerm("and", valid, tagsNameVariants(payload))
				}
			}
		}
		valid = binaryTerm("and", valid, names)
	case oakRecord:
		for _, f := range v.typ.fields {
			valid = binaryTerm("and", valid, tagsNameVariants(v.fields[f.name]))
		}
	case oakArray:
		for _, element := range v.elems {
			valid = binaryTerm("and", valid, tagsNameVariants(element))
		}
	}
	return valid
}
