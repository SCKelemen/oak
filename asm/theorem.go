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
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return Decision{Kind: DecisionUndecided, Message: "no body"}
	}
	lowering := newLowering(sig)
	lowering.functions = functions
	lowering.guards = guards
	lowering.records, lowering.adts = decls.Records, decls.ADTs
	lowering.trapsTracked = true
	for _, param := range sig.Parameters {
		if _, _, ok := contractBits(param.Type); ok {
			continue
		}
		if typ, ok := lowering.oakTypeOf(param.Type); ok && typ.kind != oakScalar {
			continue // bound below as an aggregate of leaves
		}
		return Decision{Kind: DecisionUndecided,
			Message: fmt.Sprintf("parameter %s: %s is not a fixed-width scalar, record, or sum type", param.Name.Value, typeText(param.Type))}
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
		return Decision{Kind: DecisionUndecided, Message: fmt.Sprintf("the body contains %s", reason)}
	}
	if len(lowering.loops) > 0 {
		return Decision{Kind: DecisionUndecided, Message: "the body has a data-dependent loop"}
	}
	t = truncate(t, 1)
	if assume.kind != termConst || assume.value != 1 {
		// Under the tag hypothesis: the claim holds, and no trap fires.
		t = binaryTerm("or", binaryTerm("xor", assume, constTerm(1, 1)), t)
	}
	traps := make([]*term, 0, len(lowering.traps))
	for _, trap := range lowering.traps {
		trap = truncate(trap, 1)
		if assume.kind != termConst || assume.value != 1 {
			trap = binaryTerm("and", assume, trap)
		}
		traps = append(traps, trap)
	}

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

	// Witnesses first: a trapping or false case is a counterexample
	// regardless of what the canonical form would say.
	for _, env := range witnessInputs(names, widths) {
		for _, trap := range traps {
			if trap.eval(env) != 0 {
				return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count at the width, a failed assert, or a construction outside its predicate) at " + describeEnv(names, env)}
			}
		}
		if t.eval(env) != 1 {
			return Decision{Kind: DecisionRefuted, Message: "counterexample " + describeEnv(names, env)}
		}
	}
	// The variable orders run together over the same terms, and the first
	// to decide within the node budget stops the others: a proof does not
	// depend on the order, and a theorem that is small under some order is
	// decided in that order's time rather than after the others' failures.
	control := controlParams(append([]*term{t}, traps...))
	blasters := []*blaster{newBlaster(names, widths)}
	if paramGroups(names) > 1 {
		blasters = append(blasters, newGroupedBlaster(names, widths))
	}
	if len(control) > 0 && len(control) < len(names) {
		blasters = append(blasters, newControlFirstBlaster(names, widths, control))
	}
	var stop atomic.Bool
	type attempt struct {
		decision Decision
		exceeded bool
	}
	results := make(chan attempt, len(blasters))
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		go func(bl *blaster) {
			decision, exceeded := decideBlasted(bl, traps, t, names)
			results <- attempt{decision, exceeded}
		}(bl)
	}
	for range blasters {
		if a := <-results; !a.exceeded {
			stop.Store(true)
			return a.decision
		}
	}
	return Decision{Kind: DecisionUndecided, Message: "the bit-level decision exceeded its node budget"}
}

// controlParams names the parameters the terms read as control: those
// under the condition of a conditional (a selector compared to a constant,
// a guard) or the count of a shift. The rest are data, which flow into
// results and comparisons of results without choosing a branch.
func controlParams(terms []*term) map[string]bool {
	control := map[string]bool{}
	visited := map[*term]bool{}
	var walk func(t *term)
	walk = func(t *term) {
		if t == nil || visited[t] {
			return
		}
		visited[t] = true
		switch t.kind {
		case termIte:
			collectParams(t.cond, control)
			walk(t.left)
			walk(t.right)
			return
		case termBinary:
			switch t.op {
			case "shl", "shr", "lsr", "asr", "sar", "ror":
				collectParams(t.right, control)
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

// decideBlasted settles the theorem with one blaster: every recorded trap
// condition must be impossible and the claim must be the true node. The
// second result reports a blown node budget, which the caller may answer
// with another variable order.
func decideBlasted(bl *blaster, traps []*term, t *term, names []string) (Decision, bool) {
	for _, trap := range traps {
		bits := bl.blast(trap)
		if bits == nil || bl.bdd.exceeded {
			return Decision{}, true
		}
		if bits[0] != bddFalse {
			env := bl.counterexample(bits[0], bddFalse)
			return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count at the width, a failed assert, or a construction outside its predicate) at " + describeEnv(names, env)}, false
		}
	}
	bits := bl.blast(t)
	if bits == nil || bl.bdd.exceeded {
		return Decision{}, true
	}
	if bits[0] == bddTrue {
		order := ""
		if bl.grouped {
			order = ", " + bl.label
		}
		return Decision{Kind: DecisionProven, Message: fmt.Sprintf("at the bit level (%d BDD nodes%s)", len(bl.bdd.nodes), order)}, false
	}
	env := bl.counterexample(bits[0], bddTrue)
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
