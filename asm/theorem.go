package asm

import (
	"fmt"
	"sort"

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

// DecideTheorem decides a theorem declaration: every parameter a
// fixed-width scalar or Bool, the body in the verifier's subset (wrapping
// arithmetic, bitwise operators, comparisons, conditionals, typed locals,
// counted loops, calls to program functions in the same subset — given in
// functions — inlined; no views or data-dependent loops).
func DecideTheorem(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement) Decision {
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return Decision{Kind: DecisionUndecided, Message: "no body"}
	}
	for _, param := range sig.Parameters {
		if _, _, ok := contractBits(param.Type); !ok {
			return Decision{Kind: DecisionUndecided,
				Message: fmt.Sprintf("parameter %s: %s is not a fixed-width scalar", param.Name.Value, typeText(param.Type))}
		}
	}
	lowering := newLowering(sig)
	lowering.functions = functions
	lowering.trapsTracked = true
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
	traps := make([]*term, 0, len(lowering.traps))
	for _, trap := range lowering.traps {
		traps = append(traps, truncate(trap, 1))
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
				return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count reaches the width) at " + describeEnv(names, env)}
			}
		}
		if t.eval(env) != 1 {
			return Decision{Kind: DecisionRefuted, Message: "counterexample " + describeEnv(names, env)}
		}
	}
	bl := newBlaster(names, widths)
	// Every recorded trap condition must be impossible.
	for _, trap := range traps {
		bits := bl.blast(trap)
		if bits == nil || bl.bdd.exceeded {
			return Decision{Kind: DecisionUndecided, Message: "the bit-level decision exceeded its node budget"}
		}
		if bits[0] != bddFalse {
			env := bl.counterexample(bits[0], bddFalse)
			return Decision{Kind: DecisionRefuted, Message: "the body traps (a shift count reaches the width) at " + describeEnv(names, env)}
		}
	}
	bits := bl.blast(t)
	if bits == nil || bl.bdd.exceeded {
		return Decision{Kind: DecisionUndecided, Message: "the bit-level decision exceeded its node budget"}
	}
	if bits[0] == bddTrue {
		return Decision{Kind: DecisionProven, Message: fmt.Sprintf("at the bit level (%d BDD nodes)", len(bl.bdd.nodes))}
	}
	env := bl.counterexample(bits[0], bddTrue)
	return Decision{Kind: DecisionRefuted, Message: "counterexample " + describeEnv(names, env)}
}
