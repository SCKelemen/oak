package asm

import (
	"fmt"
	"testing"
)

// ident's culprit (the probe's dump): reads of `ew` and of the loop's
// memory `loop1.ew` at the string builder's state cells, selected under
// the lookup's outcome, and an adder equality against a read's value.
func TestIdentShapeBlast(t *testing.T) {
	id, rnames, state, strs, strings := paramTerm("id", 32), paramTerm("le.rnames_at", 32), paramTerm("le.state_at", 32), paramTerm("le.strs_at", 32), paramTerm("raw.strings_at", 32)
	names := []string{"id", "le.rnames_at", "le.state_at", "le.strs_at", "raw.strings_at"}
	widths := map[string]int{"id": 32, "le.rnames_at": 32, "le.state_at": 32, "le.strs_at": 32, "raw.strings_at": 32}
	ew := func(index *term) *term { return selectTerm("ew", index, 32) }
	lew := func(index *term) *term { return selectTerm("loop1.ew", index, 32) }
	at := func(k uint64) *term { return binaryTerm("add", state, constTerm(k, 32)) }
	none := constTerm(0xFFFFFFFF, 32)
	b1 := func(t *term) *term { return truncate(t, 1) }
	eq := func(a, b *term) *term { return b1(cmpTerm("eq", a, b)) }
	and := func(a, b *term) *term { return binaryTerm("and", a, b) }
	or := func(a, b *term) *term { return binaryTerm("or", a, b) }

	failed := and(and(b1(cmpTerm("hs", id, constTerm(65536, 32))), eq(ew(state), constTerm(0, 32))), eq(binaryTerm("add", rnames, id), state))
	found := iteTerm(b1(cmpTerm("lo", id, constTerm(65536, 32))), iteTerm(failed, constTerm(905, 32), ew(binaryTerm("add", rnames, id))), none)
	a := and(eq(found, none), b1(cmpTerm("lo", id, constTerm(65536, 32))))
	rxLen := selectTerm("rx", binaryTerm("add", binaryTerm("add", strings, binaryTerm("shl", id, constTerm(1, 32))), constTerm(1, 32)), 32)
	b := and(a, b1(cmpTerm("lo", constTerm(0, 32), rxLen)))
	v16 := iteTerm(b, lew(at(16)), iteTerm(and(a, eq(ew(at(16)), none)), ew(at(9)), ew(at(16))))
	v8 := iteTerm(b, lew(at(8)), ew(at(8)))
	v9 := iteTerm(b, lew(at(9)), ew(at(9)))
	notFull := binaryTerm("xor", or(eq(v16, none), b1(cmpTerm("hs", v8, constTerm(524288, 32)))), constTerm(1, 1))
	cond := and(and(a, notFull), eq(at(9), binaryTerm("add", strs, binaryTerm("shl", v8, constTerm(1, 32)))))
	culprit := iteTerm(cond, v16, v9)

	measure := func(label string, term *term) int {
		bl := newBlaster(names, widths)
		bl.bdd = newBDD(loopDecisionNodeBudget)
		bits := bl.blast(term)
		if bits != nil && !bl.bdd.exceeded {
			bl.consistency()
		}
		fmt.Printf("%-44s %8d diagram nodes (exceeded=%v)\n", label, len(bl.bdd.nodes), bl.bdd.exceeded)
		return len(bl.bdd.nodes)
	}
	measure("found", found)
	measure("a (found eq NONE and in range)", a)
	measure("b (a and the name is not empty)", b)
	measure("v8", v8)
	measure("v16", v16)
	measure("notFull", notFull)
	measure("adder equality state+9 == strs+(v8<<1)", eq(at(9), binaryTerm("add", strs, binaryTerm("shl", v8, constTerm(1, 32)))))
	measure("cond", cond)
	// 754,007 nodes at the measurement (2026-10-06): the adder equality
	// over a read selected by `b` carries b's whole condition into every
	// carry, and the conditional over cond multiplies it again. The shape
	// must stay within one decision's budget; a case split on b is the
	// step that would make it small.
	if got := measure("culprit ite(cond, v16, v9)", culprit); got >= loopDecisionNodeBudget {
		t.Fatalf("ident's culprit exceeds one decision's budget (%d nodes)", got)
	}
	if got := premiseSelectCondition(culprit); !equalTerms(got, b) {
		t.Fatalf("premise split condition = %s, want the shared read selector %s", got, b)
	}
	singleChoice := iteTerm(b, lew(at(8)), ew(at(8)))
	if got := premiseSelectCondition(eq(singleChoice, none)); got != nil {
		t.Fatalf("one selected read requested an eager split on %s", got)
	}
	mixed1 := iteTerm(b, lew(at(8)), none)
	mixed2 := iteTerm(b, lew(at(9)), none)
	if got := premiseSelectCondition(and(eq(mixed1, none), eq(mixed2, none))); got != nil {
		t.Fatalf("non-read alternatives requested an eager split on %s", got)
	}

	// The equality itself is deliberately tautological only under its
	// premise. Without fixing b first, the premise and the repeated culprit
	// together exceed one loop decision's diagram allowance; under each arm
	// the selected reads are plain reads and the implication decides.
	premise := eq(culprit, v9)
	budget := &nodeBudget{remaining: loopProofNodeBudget, loop: true}
	if holds, decided := impliesEqualWithin(premise, culprit, v9, func(name string) int { return widths[name] }, budget); !decided || !holds {
		t.Fatalf("split implication: holds=%v decided=%v, budget remaining %d", holds, decided, budget.remaining)
	}
}
