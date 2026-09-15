package asm

import (
	"fmt"
	"testing"
)

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

// The negation of a comparison canonicalizes to the opposite comparison:
// the Oak body's `here < found` and the machine's `not (here >= found)`
// (a branch taken the other way) are one term, and notTerm spells a
// comparison's negation the same way; a double negation is the
// comparison itself.
func TestCanonicalNegatedComparison(t *testing.T) {
	here, found := paramTerm("here", 32), paramTerm("found", 32)
	lo := truncate(cmpTerm("lo", here, found), 1)
	hs := truncate(cmpTerm("hs", here, found), 1)
	if got := canonical(binaryTerm("xor", hs, constTerm(1, 1))); !equalTerms(got, lo) {
		t.Fatalf("not (here hs found) canonicalizes to %s, want %s", got, lo)
	}
	if got := canonical(binaryTerm("xor", constTerm(1, 1), hs)); !equalTerms(got, lo) {
		t.Fatalf("xor with the constant first: %s, want %s", got, lo)
	}
	if got := canonical(notTerm(notTerm(cmpTerm("eq", here, found)))); !equalTerms(got, truncate(cmpTerm("eq", here, found), 1)) {
		t.Fatalf("double negation: %s", got)
	}
	if got := notTerm(cmpTerm("hs", here, found)); !equalTerms(got, lo) {
		t.Fatalf("notTerm of a comparison: %s, want %s", got, lo)
	}
	// A one-bit parameter has no opposite comparison: its negation stays.
	if got := canonical(notTerm(paramTerm("p", 1))); got.kind != termBinary || got.op != "xor" {
		t.Fatalf("negated parameter: %s", got)
	}
}

// The boolean algebra a machine's branches leave behind folds: a path
// condition joined with its complement is a tautology or a
// contradiction, a conditional with one value on both arms is that
// value, and the conjunct that was a tautology drops out.
func TestCanonicalComplementaryConditions(t *testing.T) {
	x, n := paramTerm("x", 32), paramTerm("n", 32)
	eq, ne := truncate(cmpTerm("eq", x, n), 1), truncate(cmpTerm("ne", x, n), 1)
	if got := canonical(binaryTerm("or", ne, eq)); got.kind != termConst || got.value != 1 {
		t.Fatalf("x != n or x == n: %s", got)
	}
	if got := canonical(binaryTerm("and", eq, binaryTerm("xor", eq, constTerm(1, 1)))); got.kind != termConst || got.value != 0 {
		t.Fatalf("c and not c: %s", got)
	}
	if got := canonical(binaryTerm("and", eq, binaryTerm("or", ne, eq))); !equalTerms(got, eq) {
		t.Fatalf("a conjunct with a tautology: %s, want %s", got, eq)
	}
	if got := canonical(iteTerm(eq, binaryTerm("add", x, constTerm(1, 32)), binaryTerm("add", x, constTerm(1, 32)))); !equalTerms(got, binaryTerm("add", x, constTerm(1, 32))) {
		t.Fatalf("one value on both arms: %s", got)
	}
	if got := canonical(binaryTerm("and", eq, constTerm(0, 1))); got.kind != termConst || got.value != 0 {
		t.Fatalf("and with zero: %s", got)
	}
}

// A 1/0 value's spellings meet: the machine's `cset` of a condition is
// the condition, its zero test is the value (or its negation), and a
// truncation through a mask covering the width is a truncation.
func TestCanonicalBooleanValued(t *testing.T) {
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	c := cmpTerm("ne", x, y) // width 32, a 1/0 value
	cset := iteTerm(c, constTerm(1, 32), constTerm(0, 32))
	if got := canonical(cset); !equalTerms(got, c) {
		t.Fatalf("cset: %s, want %s", got, c)
	}
	if got := canonical(cmpTerm("ne", cset, constTerm(0, 32))); !equalTerms(got, c) {
		t.Fatalf("cset != 0: %s, want %s", got, c)
	}
	if got := canonical(cmpTerm("eq", binaryTerm("or", c, cmpTerm("ne", y, x)), constTerm(0, 32))); got.kind != termBinary || got.op != "xor" {
		t.Fatalf("(c or d) == 0: %s", got)
	}
	// A sum is not 1/0: its zero test stays a comparison.
	if got := canonical(cmpTerm("ne", binaryTerm("add", x, y), constTerm(0, 32))); got.kind != termCmp {
		t.Fatalf("sum != 0: %s", got)
	}
	p, q := paramTerm("p", 64), paramTerm("q", 64)
	if got := truncate(binaryTerm("and", binaryTerm("add", p, q), constTerm(0xFFFFFFFF, 64)), 32); !equalTerms(got, truncate(binaryTerm("add", p, q), 32)) {
		t.Fatalf("masked then truncated: %s", got)
	}
	// Over a parameter the mask stays: its extension back would forget it.
	if got := truncate(binaryTerm("and", p, constTerm(0xFFFFFFFF, 64)), 32); equalTerms(got, paramTerm("p", 32)) || zeroExtend(got, 64).eval(map[string]uint64{"p": 1 << 40}) != 0 {
		t.Fatalf("a masked parameter truncated: %s", got)
	}
	// The machine's any (a reduction, cset, cmp #0) and the Oak side's
	// (an or of lane tests) are equal reductions after the cset rule.
	l0, l1 := paramTerm("l0", 8), paramTerm("l1", 8)
	oak := binaryTerm("or", truncate(cmpTerm("ne", l0, constTerm(0, 8)), 1), truncate(cmpTerm("ne", l1, constTerm(0, 8)), 1))
	machine := cmpTerm("ne", iteTerm(binaryTerm("or", zeroExtend(cmpTerm("ne", l1, constTerm(0, 8)), 32), zeroExtend(cmpTerm("ne", l0, constTerm(0, 8)), 32)), constTerm(1, 32), constTerm(0, 32)), constTerm(0, 32))
	if !equalReductions(oak, truncate(machine, 1)) || !equalReductions(oak, truncate(canonical(machine), 1)) {
		t.Fatalf("any spelled both ways: %s vs %s", oak, canonical(machine))
	}
}

// A premise of exit facts binding a dozen symbols to terms (`g = (total +
// 15) >> 4`) is satisfied by no random valuation; settled through its
// bindings, a valuation refutes an obligation over two distinct symbols
// (a wrong pairing's `off = found`) instead of leaving it to a diagram.
func TestRefutedByValuationSettlesPremiseBindings(t *testing.T) {
	total, g, off, found := paramTerm("total", 32), paramTerm("loop16.g", 32), paramTerm("loop15.off", 32), paramTerm("loop15.found", 32)
	groups := binaryTerm("shr", binaryTerm("add", total, constTerm(15, 32)), constTerm(4, 32))
	premise := binaryTerm("and", truncate(cmpTerm("ls", g, groups), 1), truncate(cmpTerm("hs", g, groups), 1))
	for k := 0; k < 12; k++ {
		x := paramTerm(fmt.Sprintf("loop%d.j", 17+k), 32)
		premise = binaryTerm("and", premise, binaryTerm("and", truncate(cmpTerm("ls", x, g), 1), truncate(cmpTerm("hs", x, g), 1)))
	}
	premise = binaryTerm("and", premise, notTerm(cmpTerm("lo", off, binaryTerm("sub", paramTerm("len(bytes)", 32), constTerm(66, 32)))))
	names := []string{"total", "loop16.g", "loop15.off", "loop15.found", "len(bytes)"}
	widths := map[string]int{}
	for _, name := range names {
		widths[name] = 32
	}
	for k := 0; k < 12; k++ {
		name := fmt.Sprintf("loop%d.j", 17+k)
		names = append(names, name)
		widths[name] = 32
	}
	if bindings := premiseBindings(premise); len(bindings) != 2+12*2+1 {
		t.Fatalf("bindings: %d", len(bindings))
	}
	if !refutedByValuation(premise, off, found, names, widths) {
		t.Fatal("off = found under the exit facts must be refuted by a settled valuation")
	}
	// The same premise does not refute what holds under it.
	if refutedByValuation(premise, g, groups, names, widths) {
		t.Fatal("g = groups holds under the premise")
	}
}

// The machine's `eor w, w, #1` of a 1/0 word, its bit taken and negated
// again, is the word's own or of lane tests: the truncation distributes
// over the bitwise combination and the double negation folds, so the
// reductions meet as one shape.
func TestCanonicalBitOfBooleanCombination(t *testing.T) {
	l0, l1 := paramTerm("l0", 8), paramTerm("l1", 8)
	any32 := binaryTerm("or", zeroExtend(cmpTerm("ne", l0, constTerm(0, 8)), 32), zeroExtend(cmpTerm("ne", l1, constTerm(0, 8)), 32))
	machine := binaryTerm("xor", truncate(binaryTerm("xor", any32, constTerm(1, 32)), 1), constTerm(1, 1))
	got := canonical(machine)
	oak := binaryTerm("or", truncate(cmpTerm("ne", l0, constTerm(0, 8)), 1), truncate(cmpTerm("ne", l1, constTerm(0, 8)), 1))
	if !equalTerms(got, oak) && !equalReductions(got, oak) {
		t.Fatalf("machine any: %s, want %s", got, oak)
	}
	// A truncation of a sum is not distributed: a sum is not a 1/0 value.
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	if got := canonical(truncate(binaryTerm("add", x, y), 1)); got.kind != termBinary || got.op != "and" {
		t.Fatalf("bit of a sum: %s", got)
	}
}
