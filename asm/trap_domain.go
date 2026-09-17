package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// verifyTrapDomain admits a non-loop value/effect proof only after proving
// that every excluded machine-trap input also traps in the source. The
// ordinary proof's !machineTrap premise must NEVER enter this obligation:
// it would make the very claim being checked vacuous.
//
// This is a one-way, partial-correctness obligation, not equality of trap
// behavior, exception handlers, or effects before a trap. Summarized loops
// retain their existing verifier contract; their per-iteration trap-domain
// obligations need a separate extension to the coupling proof.
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
	proof := decideEqual(fn, source, bad, constTerm(0, 1), 1, " (machine trap-domain obligation)")
	if proof.Kind != VerdictProven {
		// The collected traps may be incomplete for a construct outside
		// this slice. A failed obligation is not itself a concrete source
		// counterexample; preserve the separate witness mismatch check.
		return unproven(proof.Message)
	}
	return result
}
