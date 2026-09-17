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
func decideLoopTrapDomains(exec *pathExecutor, source *oakLowering, sigma map[string]*term, implies func(*term, *term, *term) (bool, bool)) (string, bool) {
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
	check := func(premise, machineTrap, oakTrap *term) bool {
		bad := binaryTerm("and", trapOrFalse(substitute(machineTrap, sigma)), notTerm(trapOrFalse(oakTrap)))
		holds, decided := implies(premise, bad, constTerm(0, 1))
		if (!decided || !holds) && os.Getenv("OAK_VERIFY_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "verify loop trap domain: decided=%v premise=%s machine=%s oak=%s\n", decided, premise, trapOrFalse(substitute(machineTrap, sigma)), trapOrFalse(oakTrap))
		}
		return decided && holds
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
