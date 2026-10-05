package asm

import (
	"fmt"
	"os"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

func trapOrFalse(trap *term) *term {
	if trap == nil {
		return constTerm(0, 1)
	}
	return truncate(trap, 1)
}

func disjoinTraps(traps []*term) *term {
	var result *term
	for _, trap := range traps {
		if result == nil {
			result = truncate(trap, 1)
		} else {
			result = binaryTerm("or", result, truncate(trap, 1))
		}
	}
	return result
}

// nil sink is used only for the frame-slot discovery probe, whose traps
// are collected afresh during the actual symbolic iteration.
func recordLoopTrap(sink **term, path, taken *term) {
	if sink == nil {
		return
	}
	trap := binaryTerm("and", truncate(path, 1), truncate(taken, 1))
	if *sink == nil {
		*sink = trap
	} else {
		*sink = binaryTerm("or", *sink, trap)
	}
}

// firstIterationTrap projects only a reached loop's first header/body to
// the surrounding source scope. Body predicates require source entry.
// A residual state of this loop or a nested loop is not an entry fact.
func firstIterationTrap(ev *loopEvent, lastLoop int) (*term, bool) {
	trap := binaryTerm("or", trapOrFalse(ev.headerTrap), binaryTerm("and", truncate(ev.cond, 1), trapOrFalse(ev.bodyTrap)))
	entry, known := ev.entryPredicate(trap)
	if !known {
		return nil, false
	}
	seen := map[*term]bool{}
	var closed func(*term) bool
	closed = func(t *term) bool {
		if t == nil || seen[t] {
			return true
		}
		seen[t] = true
		if t.kind == termParam || t.kind == termSelect {
			for k := ev.index; k <= lastLoop; k++ {
				prefix := fmt.Sprintf("loop%d", k)
				if strings.HasPrefix(t.name, prefix+".") || strings.HasPrefix(t.name, prefix+"[") {
					return false
				}
			}
		}
		return closed(t.cond) && closed(t.left) && closed(t.right)
	}
	if !closed(entry) {
		return nil, false
	}
	return entry, true
}

// decideLoopTrapDomains uses the selected coupling, but no machine path
// condition, no !machineTrap premise, and no loop exit premise. Its
// deliberately stronger source-only premises avoid circular admission.
func decideLoopTrapDomains(exec *pathExecutor, source *oakLowering, sigma map[string]*term, newImplies func() func(*term, *term, *term) (bool, bool)) (string, bool) {
	if !source.trapDomainTracked {
		return "source loop traps were not collected", false
	}
	// The only input-domain restriction here is well-typed source tags.
	domainSource := *source
	domainSource.machineTrap = nil
	typed := domainSource.domainCondition()
	if typed == nil {
		typed = constTerm(1, 1)
	}
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	// smallTraps is the disjunction of a trap term's disjuncts of at most
	// smallTrapNodes nodes: implying it implies the whole, and a machine
	// end is usually one of them (`len(tables) < 16` against `16 >
	// len(tables)`), where one large source trap (a path through a nest of
	// loops, four million nodes in literals.oak's count) ran the diagram out.
	smallTraps := func(t *term) (*term, bool) {
		all := disjunctsOf(t)
		var out *term
		for _, d := range all {
			if termSize(d, map[*term]int{}) > smallTrapNodes {
				continue
			}
			if out == nil {
				out = d
			} else {
				out = binaryTerm("or", out, d)
			}
		}
		return out, out != nil && len(all) > 1
	}
	// The shared allowance decides the obligations as before; an end's
	// first try against the small source traps decides under an allowance
	// of its own, since those terms are small and the shared one may be
	// spent by a large source trap met earlier (a ninety-node end of
	// literals.oak's count came back undecided with nothing left).
	implies := newImplies()
	check := func(premise, machineTrap, oakTrap *term) bool {
		machine, oak := dropUnreachableTraps(trapOrFalse(substitute(machineTrap, sigma))), trapOrFalse(oakTrap)
		bad := binaryTerm("and", machine, notTerm(oak))
		if holds, decided := implies(premise, bad, constTerm(0, 1)); decided && holds {
			return true
		}
		// The whole disjunction of trapping ends against the whole
		// disjunction of source traps exceeds the diagrams around a walker
		// (map_page's fourteen ends); as verifyTrapDomain decides the
		// non-loop obligation, each machine end is decided on its own: the
		// end's path is a premise, under which the implication decider
		// settles the source traps' guards from the path's facts before
		// any diagram, and the claim is that some source trap holds there.
		for k, end := range trapDisjuncts(bad) {
			if end.kind == termBinary && end.op == "and" {
				path := binaryTerm("and", premise, end.left)
				// The syntactic decision first: it costs a walk, where the
				// diagrams over a walker's end ran for minutes.
				if sourceTrapOnPath(path, oak) {
					continue
				}
				if small, some := smallTraps(oak); some {
					if holds, decided := newImplies()(path, small, constTerm(1, 1)); decided && holds {
						continue
					}
				}
				if holds, decided := implies(path, oak, constTerm(1, 1)); decided && holds {
					continue
				}
			}
			if holds, decided := implies(premise, end, constTerm(0, 1)); decided && holds {
				continue
			}
			if trace {
				fmt.Fprintf(os.Stderr, "verify loop trap domain: end %d undecided (end kind %d op %s; %d source traps); premise=%s machine=%s oak=%s\n", k, end.kind, end.op, len(source.traps), premise, machine, oak)
			}
			return false
		}
		return true
	}
	for k, machine := range exec.loops {
		oak := source.loops[k]
		premise := typed
		for at := k; at >= 0; at = source.loops[at].parent - 1 {
			ev := source.loops[at]
			if ev.oakPath != nil {
				premise = binaryTerm("and", premise, truncate(ev.oakPath, 1))
			}
			if at != k {
				premise = binaryTerm("and", premise, truncate(ev.cond, 1))
			}
		}
		if !check(premise, machine.headerTrap, oak.headerTrap) {
			return fmt.Sprintf("loop %d header trap-domain obligation is not proven", k+1), false
		}
		bodyPremise := binaryTerm("and", premise, truncate(oak.cond, 1))
		// A source header trap also prevents this iteration from returning.
		oakTrap := binaryTerm("or", trapOrFalse(oak.headerTrap), trapOrFalse(oak.bodyTrap))
		if !check(bodyPremise, machine.bodyTrap, oakTrap) {
			return fmt.Sprintf("loop %d body trap-domain obligation is not proven", k+1), false
		}
	}
	if !check(typed, exec.trap, disjoinTraps(source.traps)) {
		return "root trap-domain obligation around the loops is not proven", false
	}
	return "", true
}

// dropUnreachableTraps removes from a trap disjunction the comparisons
// against a constant that the range bound (asm/range.go) shows never
// hold: the machine guards a data-dependent shift count at the width
// (`cmp count, #32; b.hs trap`) and the guard's condition enters its trap
// domain, where the Oak side folded the same trap away by the bound
// (`((x & 3) << 3) < 32` for a byte extract, the prover's str_less). Left
// in, the constant-false disjunct still stood in the diagram beside the
// element selects and the obligation ran out of nodes.
func dropUnreachableTraps(t *term) *term {
	disjuncts := disjunctsOf(t)
	kept := make([]*term, 0, len(disjuncts))
	for _, d := range disjuncts {
		if d.kind == termCmp && d.right != nil && d.right.kind == termConst {
			bound := maxValue(d.left)
			switch d.op {
			case "hs", "cs":
				if bound < d.right.value {
					continue // never at least the constant
				}
			case "hi":
				if bound <= d.right.value {
					continue // never above the constant
				}
			}
		}
		kept = append(kept, d)
	}
	if len(kept) == len(disjuncts) {
		return t
	}
	if len(kept) == 0 {
		return constTerm(0, 1)
	}
	out := kept[0]
	for _, d := range kept[1:] {
		out = binaryTerm("or", out, d)
	}
	return out
}

// smallTrapNodes bounds the source trap disjuncts a machine trap end is
// first decided against (decideLoopTrapDomains).
const smallTrapNodes = 4096

// verifyTrapDomain admits a non-loop value/effect proof only after proving
// that every excluded machine-trap input also traps in the source. The
// ordinary proof's !machineTrap premise must NEVER enter this obligation:
// it would make the very claim being checked vacuous.
//
// This is a one-way, partial-correctness obligation, not equality of trap
// behavior, exception handlers, or effects before a trap. Summarized loops
// check their root and per-iteration scopes in decideLoopTrapDomains after
// selecting the coupling, before admitting any value/effect proof.
func verifyTrapDomain(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, result Verdict) Verdict {
	if result.Kind != VerdictProven || exec == nil || exec.trap == nil || len(exec.loops) != 0 {
		return result
	}
	unproven := func(reason string) Verdict {
		return verdictWithCallees(Verdict{
			Kind:    VerdictWitnessed,
			Message: fmt.Sprintf("asm unit %s: value/effect comparison proven (evidence, not proof: the machine trap-domain obligation is not proven; %s)", fn.Name, reason),
		}, result.Callees)
	}
	source := prepareLowering(fn, sig, nil)
	source.trapDomainTracked = true
	source.resultChunk = exec.resultChunk
	if exec.notes != nil {
		source.shiftGuardMax = exec.notes.shiftGuardMax
	}
	for name, width := range exec.freshSyms {
		source.fresh[name] = width
	}
	var reason string
	var ok bool
	if _, isVector := vectorShape(sig.ReturnType); isVector {
		typ, modeled := source.oakTypeOf(sig.ReturnType)
		if !modeled {
			return unproven("a vector result type without a model")
		}
		_, reason, ok = source.aggregateValue(oakBody, typ)
	} else if exec.hasResult {
		words := 1
		if exec.resultArea != nil && exec.resultChunks > 1 {
			words = exec.resultChunks
		}
		_, _, reason, ok = source.resultTerms(fn, sig, oakBody, words)
	} else {
		reason, ok = source.lowerUnitBody(oakBody)
	}
	if !ok {
		return unproven("source trap lowering contains " + reason)
	}
	if len(source.loops) != 0 {
		return unproven("source trap lowering requires a loop invariant")
	}
	oakTrap := constTerm(0, 1)
	for _, trap := range source.traps {
		oakTrap = binaryTerm("or", oakTrap, truncate(trap, 1))
	}
	bad := binaryTerm("and", truncate(exec.trap, 1), notTerm(oakTrap))
	// source.machineTrap is nil. Only well-typed input restrictions (union
	// tags) and the decider's memory-read consistency restrict this proof.
	//
	// The machine trap is the disjunction of its trapping ends' path
	// conditions (runAll), and a disjunction is false exactly when every
	// disjunct is: the obligation decides end by end, each a conjunction
	// of branch conditions along one path against the Oak traps, where
	// the whole exceeded the diagrams (protocol_line_done's seven guarded
	// pushes trap on 14 ends).
	trace := os.Getenv("OAK_VERIFY_TRACE") != ""
	for k, end := range trapDisjuncts(bad) {
		// An end's condition is a premise: the machine's path to its trap
		// implies an Oak trap. The implication decider (the loop prover's)
		// settles the Oak traps' guards from the path's facts and prunes
		// the reads' chains under them before any diagram, where the flat
		// decision blasted the chains whole and exceeded its budget on
		// protocol_line_done's stack pointer read back after each push.
		if end.kind == termBinary && end.op == "and" {
			// The syntactic decision first (sourceTrapOnPath, as the loop
			// obligations decide their ends): a walk over the end's path
			// and the source traps, where the diagrams over unmap_page's
			// ends exceeded their budget.
			if sourceTrapOnPath(end.left, oakTrap) {
				if trace {
					fmt.Fprintf(os.Stderr, "verify %s: trap-domain end %d proven on its path\n", fn.Name, k)
				}
				continue
			}
			if holds, decided := impliesEqual(end.left, notTerm(end.right), constTerm(1, 1), source.declaredWidth); decided && holds {
				if trace {
					fmt.Fprintf(os.Stderr, "verify %s: trap-domain end %d proven by implication\n", fn.Name, k)
				}
				continue
			}
		}
		proof := decideEqual(fn, source, end, constTerm(0, 1), 1, " (machine trap-domain obligation)")
		if trace {
			fmt.Fprintf(os.Stderr, "verify %s: trap-domain end %d: %s\n", fn.Name, k, proof.Message)
		}
		if proof.Kind != VerdictProven {
			// The collected traps may be incomplete for a construct
			// outside this slice. A failed obligation is not itself a
			// concrete source counterexample; preserve the separate
			// witness mismatch check.
			return unproven(proof.Message)
		}
	}
	return result
}

// sourceTrapOnPath decides, without a diagram, that some source trap
// holds on a machine trap end's path: the source traps pruned under the
// path's facts and respelled (the span case split's canonicalLinear, to a
// fixpoint) are compared disjunct by disjunct with the path's conjuncts
// respelled the same way. The machine's bound on a page-table leaf index
// (`((d and mask) sub base) shr 14) and 0xFFFFFFFF) and 65535) hs 4`) and
// the Oak side's (`… and 65535) and 65535) hs 4`) are one term once the
// masks are folded, where their bit-level implication exceeded the
// budget. A disjunct that is the constant 1 after pruning holds outright.
func sourceTrapOnPath(path, oak *term) bool {
	return sourceTrapOnPathDepth(path, oak, sourceTrapSplitDepth)
}

// sourceTrapSplitDepth bounds the conditional facts a path is split on:
// a machine end whose path holds `(c ? X : Y)` as a fact is two paths,
// `c and X` and `not c and Y`, each of which must reach a source trap.
const sourceTrapSplitDepth = 8

func sourceTrapOnPathDepth(path, oak *term, depth int) bool {
	// Respelled before pruning: the machine's index masks and the Oak
	// side's meet only once both are in the one spelling, and the facts
	// are read from the respelled path.
	cmemo, cbool := map[*term]*term{}, map[*term]bool{}
	path = respell(canonicalMemo(truncate(path, 1), cmemo, cbool))
	oak = respell(canonicalMemo(truncate(oak, 1), cmemo, cbool))
	// Each conjunct of the path is settled by the others (a call
	// summary's result carries the callee's branch as a conditional, and
	// the path holds the branch as a fact), then respelled again.
	facts := conjunctsOf(path)
	// Each fact's conditionals are settled by the other facts' spellings
	// first (`(d0 invalid ? free_count ne 0 : 1)` under the fact `d0
	// invalid`), so only a conditional the path leaves open is split on.
	for i := range facts {
		others := make([]*term, 0, len(facts)-1)
		others = append(others, facts[:i]...)
		others = append(others, facts[i+1:]...)
		facts[i] = respell(canonicalMemo(truncate(settleBySpelling(facts[i], others), 1), cmemo, cbool))
	}
	facts = conjunctsOf(conjoinAll(facts))
	for i, fact := range facts {
		if fact.kind == termIte && depth > 0 {
			rest := make([]*term, 0, len(facts))
			rest = append(rest, facts[:i]...)
			rest = append(rest, facts[i+1:]...)
			taken := append(append([]*term{}, rest...), truncate(fact.cond, 1), truncate(fact.left, 1))
			skipped := append(append([]*term{}, rest...), notTerm(truncate(fact.cond, 1)), truncate(fact.right, 1))
			return sourceTrapOnPathDepth(conjoinAll(taken), oak, depth-1) && sourceTrapOnPathDepth(conjoinAll(skipped), oak, depth-1)
		}
	}
	for i, fact := range facts {
		var others *term
		for j, other := range facts {
			if j == i {
				continue
			}
			if others == nil {
				others = other
			} else {
				others = binaryTerm("and", others, other)
			}
		}
		if others != nil {
			facts[i] = respell(canonicalMemo(truncate(pruneUnderFacts(others, []*term{fact})[0], 1), cmemo, cbool))
		}
	}
	path = facts[0]
	for _, fact := range facts[1:] {
		if fact.kind == termConst && fact.value&1 == 0 {
			// A conjunct the others refute: the path is infeasible (the
			// executor keeps such ends in the trap disjunction) and traps
			// nowhere.
			return true
		}
		path = binaryTerm("and", path, fact)
	}
	if facts[0].kind == termConst && facts[0].value&1 == 0 {
		return true
	}
	pruned := pruneUnderFacts(path, []*term{oak})[0]
	// The facts settle the source traps' conditionals by spelling too:
	// the pruner's structural match is bounded (sameTermBudget), and a
	// page-table index runs past it, so `(leaf eq root) ? 0 : guard`
	// under the fact `leaf ne root` was left in place.
	settled := settleBySpelling(respell(canonicalMemo(truncate(pruned, 1), cmemo, cbool)), facts)
	traps := disjunctsOf(respell(canonicalMemo(truncate(settled, 1), cmemo, cbool)))
	// Spellings compare as text: a comparison is read at one bit on one
	// side and at its operands' width on the other, and equalTerms keeps
	// the widths apart where the value is the same.
	spelled := make([]string, len(facts))
	for i, f := range facts {
		spelled[i] = f.String()
	}
	negation := func(t *term) (string, bool) {
		if t.kind == termBinary && t.op == "xor" && t.right.kind == termConst && t.right.value == 1 {
			return t.left.String(), true
		}
		if neg := negatedCmp(t); neg != nil {
			return neg.String(), true
		}
		return "", false
	}
	// A path that asserts a fact and its complement (the executor keeps
	// infeasible paths in the trap disjunction) traps nowhere: vacuous.
	for i, f := range facts {
		if not, ok := negation(f); ok {
			for j, text := range spelled {
				if j != i && text == not {
					return true
				}
			}
		}
	}
	onPath := func(t *term) bool {
		if t.kind == termConst {
			return t.value&1 == 1
		}
		text := t.String()
		for _, fact := range spelled {
			if fact == text {
				return true
			}
		}
		return false
	}
	// A source trap is a conjunction (its guards and the bound); it holds
	// on the path when each conjunct does.
	for _, trap := range traps {
		holds := true
		for _, part := range conjunctsOf(trap) {
			if !onPath(part) {
				holds = false
				break
			}
		}
		if holds {
			return true
		}
	}
	if os.Getenv("OAK_VERIFY_TRACE_TRAPS") != "" {
		// The respelled source traps and path facts of an undecided end.
		for _, trap := range traps {
			if trap.kind != termConst {
				fmt.Fprintf(os.Stderr, "  source trap: %s\n", trap)
			}
		}
		for _, fact := range spelled {
			if fact != "1" {
				fmt.Fprintf(os.Stderr, "  path fact: %s\n", fact)
			}
		}
	}
	return false
}

// settleBySpelling rewrites the one-bit conditionals and conjuncts of t
// that the facts decide by their spelling: a conditional whose condition
// is a fact takes its then-arm, one whose condition's negation is a fact
// its else-arm, and a conjunct that is a fact is 1. Spellings carry no
// widths, so a comparison read at one bit on one side and at its
// operands' width on the other still meets.
func settleBySpelling(t *term, facts []*term) *term {
	holds, refuted := map[string]bool{}, map[string]bool{}
	for _, f := range facts {
		holds[f.String()] = true
		if f.kind == termBinary && f.op == "xor" && f.right.kind == termConst && f.right.value == 1 {
			refuted[f.left.String()] = true
		}
		if neg := negatedCmp(f); neg != nil {
			refuted[neg.String()] = true
		}
	}
	memo := map[*term]*term{}
	var walk func(*term) *term
	walk = func(t *term) *term {
		if t == nil {
			return nil
		}
		if done, seen := memo[t]; seen {
			return done
		}
		out := t
		switch t.kind {
		case termIte:
			cond := walk(t.cond)
			switch text := cond.String(); {
			case holds[text]:
				out = adaptWidth(walk(t.left), t.width)
			case refuted[text]:
				out = adaptWidth(walk(t.right), t.width)
			default:
				left, right := walk(t.left), walk(t.right)
				if cond != t.cond || left != t.left || right != t.right {
					out = iteTerm(cond, left, right)
				}
			}
		case termBinary:
			if (t.op == "and" || t.op == "or") && (t.width == 1 || booleanValued(t, map[*term]bool{})) {
				left, right := walk(t.left), walk(t.right)
				value := func(x *term) *term {
					if holds[x.String()] {
						return constTerm(1, x.width)
					}
					if refuted[x.String()] {
						return constTerm(0, x.width)
					}
					return x
				}
				left, right = value(left), value(right)
				if left != t.left || right != t.right {
					out = binaryTerm(t.op, left, right)
				}
			} else {
				left, right := walk(t.left), walk(t.right)
				if left != t.left || right != t.right {
					out = binaryTerm(t.op, left, right)
				}
			}
		}
		memo[t] = out
		return out
	}
	return walk(t)
}

// disjunctsOf flattens a Boolean or-chain; conjunctsOf an and-chain (a
// Boolean read at a wider width, `(a and b) and c` over comparisons,
// flattens the same).
func disjunctsOf(t *term) []*term {
	if t.kind == termBinary && t.op == "or" && (t.width == 1 || booleanValued(t, map[*term]bool{})) {
		return append(disjunctsOf(t.left), disjunctsOf(t.right)...)
	}
	return []*term{t}
}

func conjunctsOf(t *term) []*term {
	if t.kind == termBinary && t.op == "and" && (t.width == 1 || booleanValued(t, map[*term]bool{})) {
		return append(conjunctsOf(t.left), conjunctsOf(t.right)...)
	}
	return []*term{t}
}

// conjoinAll is the and-chain of the terms (1 for none).
func conjoinAll(terms []*term) *term {
	var out *term
	for _, t := range terms {
		if out == nil {
			out = t
		} else {
			out = binaryTerm("and", out, t)
		}
	}
	if out == nil {
		return constTerm(1, 1)
	}
	return out
}

// trapDisjuncts splits `and(or(a, or(b, c)), n)` into `and(a, n)`,
// `and(b, n)`, `and(c, n)`: the machine trap's or-chain of trapping ends
// distributed over the negated Oak traps. A term of another shape is its
// own single case.
func trapDisjuncts(bad *term) []*term {
	if bad.kind != termBinary || bad.op != "and" {
		return []*term{bad}
	}
	trap, rest := bad.left, bad.right
	var ends []*term
	var walk func(t *term)
	walk = func(t *term) {
		if t.kind == termBinary && t.op == "or" {
			walk(t.left)
			walk(t.right)
			return
		}
		ends = append(ends, t)
	}
	walk(trap)
	if len(ends) == 1 {
		return []*term{bad}
	}
	out := make([]*term, len(ends))
	for k, end := range ends {
		out[k] = binaryTerm("and", end, rest)
	}
	return out
}
