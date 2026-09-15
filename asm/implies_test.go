package asm

import "testing"

// The premise `p < 16` bounds p to four bits for the decision; `q <= 255`
// to eight; a bound by another parameter narrows nothing.
func TestNarrowByPremise(t *testing.T) {
	p, q, r := paramTerm("p", 32), paramTerm("q", 32), paramTerm("r", 32)
	premise := binaryTerm("and", cmpTerm("lo", p, constTerm(16, 32)), binaryTerm("and", cmpTerm("ls", q, constTerm(255, 32)), cmpTerm("lo", r, p)))
	widths := map[string]int{"p": 32, "q": 32, "r": 32}
	narrowByPremise(premise, widths)
	if widths["p"] != 4 || widths["q"] != 8 || widths["r"] != 32 {
		t.Fatalf("widths under the premise: %v", widths)
	}
}

// In a conditional chain over an index selecting elements, the index is
// the selector; the elements, read by the test over the selected one, are
// control but not selectors.
func TestSelectorParams(t *testing.T) {
	l := paramTerm("l", 32)
	e0, e1, e2 := paramTerm("e0", 8), paramTerm("e1", 8), paramTerm("e2", 8)
	mux := iteTerm(cmpTerm("eq", l, constTerm(0, 32)), e0, iteTerm(cmpTerm("eq", l, constTerm(1, 32)), e1, e2))
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	chosen := iteTerm(cmpTerm("ne", mux, constTerm(0, 8)), x, y)
	selectors := selectorParams([]*term{chosen})
	if len(selectors) != 1 || !selectors["l"] {
		t.Fatalf("selectors: %v", selectors)
	}
	control := controlParams([]*term{chosen})
	if !control["l"] || !control["e0"] || !control["e2"] || control["x"] {
		t.Fatalf("control: %v", control)
	}
}

// A zero-extension of a conditional is a conditional of zero-extensions:
// the arms then match a wider side's arms term for term.
func TestPushMask(t *testing.T) {
	c := cmpTerm("lo", paramTerm("i", 32), constTerm(5, 32))
	x, y := binaryTerm("add", paramTerm("a", 32), paramTerm("b", 32)), paramTerm("y", 32)
	pushed := pushMask(zeroExtend(iteTerm(c, x, y), 64))
	if pushed.kind != termIte || pushed.width != 64 || !equalTerms(pushed.left, zeroExtend(x, 64)) || !equalTerms(pushed.right, paramTerm("y", 64)) {
		t.Fatalf("pushed: %s", pushed)
	}
}

// Two conditionals spelled differently — the condition negated twice, the
// arm masked at the width it was computed at — are proven equal by their
// parts, and the decision is charged to the proof's budget.
func TestImpliesEqualByArmsAndBudget(t *testing.T) {
	widthOf := func(string) int { return 32 }
	i, a, b, y := paramTerm("i", 32), paramTerm("a", 32), paramTerm("b", 32), paramTerm("y", 32)
	sum := binaryTerm("add", a, b)
	oak := zeroExtend(iteTerm(cmpTerm("lo", i, constTerm(5, 32)), sum, y), 64)
	twiceNegated := notTerm(notTerm(cmpTerm("lo", i, constTerm(5, 32))))
	asm := iteTerm(twiceNegated, binaryTerm("and", binaryTerm("add", zeroExtend(a, 64), zeroExtend(b, 64)), constTerm(mask(32), 64)), zeroExtend(y, 64))
	budget := &nodeBudget{remaining: loopProofNodeBudget}
	holds, decided := impliesEqualWithin(constTerm(1, 1), oak, asm, widthOf, budget)
	if !decided || !holds {
		t.Fatalf("the conditionals must be proven equal by their parts: holds=%v decided=%v", holds, decided)
	}
	if budget.remaining >= loopProofNodeBudget {
		t.Fatalf("the decision must be charged to the budget, remaining %d", budget.remaining)
	}
	differ := iteTerm(twiceNegated, binaryTerm("add", zeroExtend(a, 64), zeroExtend(b, 64)), zeroExtend(y, 64))
	if holds, decided := impliesEqualWithin(constTerm(1, 1), oak, differ, widthOf, nil); !decided || holds {
		t.Fatalf("an arm that carries the sum's carry past 32 bits differs: holds=%v decided=%v", holds, decided)
	}
}
