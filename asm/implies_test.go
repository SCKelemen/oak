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

// A caller normalizes a summarized u16 result before using it as an index.
// The machine result still contains the ABI's unconstrained high fragment,
// but an identical final low mask makes that fragment irrelevant. Congruence
// must compare only the bits the mask retains, rather than demand equality of
// the unmasked operands.
func TestImpliesEqualCongruentUnderLowMask(t *testing.T) {
	base, page := paramTerm("base", 64), paramTerm("page", 64)
	index := binaryTerm("shr", binaryTerm("sub", page, base), constTerm(14, 64))
	source16 := truncate(index, 16)
	source := binaryTerm("and", zeroExtend(source16, 32), constTerm(0xffff, 32))

	high := paramTerm("call#hi", 64)
	returned := binaryTerm("or",
		binaryTerm("and", index, constTerm(0xffff, 64)),
		binaryTerm("shl", high, constTerm(16, 64)),
	)
	machine32 := truncate(returned, 32)
	machine := binaryTerm("and", machine32, constTerm(0xffff, 32))
	widthOf := func(string) int { return 64 }
	budget := &nodeBudget{remaining: loopDecisionNodeBudget}
	if holds, decided := impliesEqualCongruent(constTerm(1, 1), source, machine, widthOf, budget, 0); !decided || !holds {
		t.Fatalf("masked call result must be congruent: holds=%v decided=%v\nsource: %s\nmachine: %s", holds, decided, source, machine)
	}

	// Without the caller's final mask, the high fragment is observable and
	// the values are not equal.
	if holds, decided := impliesEqual(constTerm(1, 1), zeroExtend(source16, 32), machine32, widthOf); !decided || holds {
		t.Fatalf("unmasked call result must differ: holds=%v decided=%v", holds, decided)
	}
}

func TestImpliesEqualPeelsRedundantDeclaredWidthMasks(t *testing.T) {
	dom := paramTerm("dom", 32)
	machine := truncate(binaryTerm("and", zeroExtend(dom, 64), constTerm(0xffffffff, 64)), 32)
	widthOf := func(string) int { return 64 }
	if holds, decided := impliesEqual(constTerm(1, 1), dom, machine, widthOf); !decided || !holds {
		t.Fatalf("nested masks retaining every declared u32 bit must prove equal: holds=%v decided=%v\nsource: %s\nmachine: %s", holds, decided, dom, machine)
	}

	wide := paramTerm("wide", 64)
	maskedWide := binaryTerm("and", wide, constTerm(0xffffffff, 64))
	if holds, decided := impliesEqual(constTerm(1, 1), wide, maskedWide, widthOf); !decided || holds {
		t.Fatalf("a mask that can discard high u64 bits must not prove equal: holds=%v decided=%v", holds, decided)
	}

	shifted := binaryTerm("shr", wide, constTerm(14, 64))
	left16 := binaryTerm("and", zeroExtend(truncate(shifted, 16), 32), constTerm(0xffff, 32))
	right16 := binaryTerm("and", truncate(binaryTerm("and", shifted, constTerm(0xffffffff, 64)), 32), constTerm(0xffff, 32))
	if holds, decided := impliesEqual(constTerm(1, 1), left16, right16, widthOf); !decided || !holds {
		t.Fatalf("differently nested low-16 mask chains must prove equal: holds=%v decided=%v\nleft: %s\nright: %s", holds, decided, left16, right16)
	}
	right15 := binaryTerm("and", truncate(binaryTerm("and", shifted, constTerm(0xffffffff, 64)), 32), constTerm(0x7fff, 32))
	if holds, decided := impliesEqual(constTerm(1, 1), left16, right15, widthOf); !decided || holds {
		t.Fatalf("mask chains retaining different bits must not prove equal: holds=%v decided=%v", holds, decided)
	}
}

// A u16 span update may be emitted as a wider load/add followed by a u16
// truncation. Pushing that truncation into the addition exposes the same
// modular update, after which the masked call-result index also meets.
func TestImpliesEqualNarrowArithmeticAtMaskedIndex(t *testing.T) {
	base, page := paramTerm("base", 64), paramTerm("page", 64)
	dom := paramTerm("dom", 32)
	leafWide := binaryTerm("shr", binaryTerm("sub", page, base), constTerm(14, 64))
	leaf16 := truncate(leafWide, 16)
	prefix := binaryTerm("mul", constTerm(24, 32), dom)
	sourceIndex := binaryTerm("add", prefix, zeroExtend(leaf16, 32))
	source := binaryTerm("add", selectTerm("s.entry_count", sourceIndex, 16), constTerm(1, 16))

	high := paramTerm("call#hi", 64)
	returned := binaryTerm("or",
		binaryTerm("and", leafWide, constTerm(0xffff, 64)),
		binaryTerm("shl", high, constTerm(16, 64)),
	)
	machineLeaf := binaryTerm("and", truncate(returned, 32), constTerm(0xffff, 32))
	machineIndex := binaryTerm("add", prefix, machineLeaf)
	loaded := zeroExtend(selectTerm("s.entry_count", machineIndex, 16), 64)
	machine := truncate(binaryTerm("add", loaded, constTerm(1, 64)), 16)
	widthOf := func(string) int { return 64 }

	if holds, decided := impliesEqual(constTerm(1, 1), source, machine, widthOf); !decided || !holds {
		t.Fatalf("narrow span update must prove: holds=%v decided=%v\nsource: %s\nmachine: %s", holds, decided, source, machine)
	}
	changed := truncate(binaryTerm("add", loaded, constTerm(2, 64)), 16)
	if holds, decided := impliesEqual(constTerm(1, 1), source, changed, widthOf); !decided || holds {
		t.Fatalf("changed increment must differ: holds=%v decided=%v", holds, decided)
	}
	for _, env := range []map[string]uint64{
		{"base": 0, "page": 0, "dom": 0, "call#hi": 0},
		{"base": 0x4000, "page": 0x1234_0000, "dom": 3, "call#hi": 0xffff},
	} {
		if got, want := machine.eval(env), source.eval(env); got != want {
			t.Fatalf("equivalent update differs at %v: got %d, want %d", env, got, want)
		}
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

// A comparison result is already 0/1. Comparing it with one preserves it
// for equality and negates it for inequality, in either operand order; a
// general integer expression must not enter the rule.
func TestCanonicalBooleanComparedWithOne(t *testing.T) {
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	bit := cmpTerm("eq", x, y)
	for _, op := range []string{"eq", "ne"} {
		want := canonical(bit)
		if op == "ne" {
			want = canonical(adaptWidth(notTerm(bit), 32))
		}
		for _, comparison := range []*term{
			cmpTerm(op, bit, constTerm(1, 32)),
			cmpTerm(op, constTerm(1, 32), bit),
		} {
			got := canonical(comparison)
			if !equalTerms(got, want) {
				t.Fatalf("%s canonicalized to %s, want %s", comparison, got, want)
			}
			for xv := uint64(0); xv < 3; xv++ {
				for yv := uint64(0); yv < 3; yv++ {
					env := map[string]uint64{"x": xv, "y": yv}
					if got.eval(env) != comparison.eval(env) {
						t.Fatalf("%s changed at %v", comparison, env)
					}
				}
			}
		}
	}
	for _, constant := range []uint64{2, 4, 5} {
		for _, op := range []string{"eq", "ne"} {
			want := uint64(0)
			if op == "ne" {
				want = 1
			}
			for _, comparison := range []*term{
				cmpTerm(op, bit, constTerm(constant, 32)),
				cmpTerm(op, constTerm(constant, 32), bit),
			} {
				got := canonical(comparison)
				if got.kind != termConst || got.value != want {
					t.Fatalf("%s canonicalized to %s, want %d", comparison, got, want)
				}
				for xv := uint64(0); xv < 3; xv++ {
					for yv := uint64(0); yv < 3; yv++ {
						env := map[string]uint64{"x": xv, "y": yv}
						if got.eval(env) != comparison.eval(env) {
							t.Fatalf("%s changed at %v", comparison, env)
						}
					}
				}
			}
		}
	}
	sum := binaryTerm("add", x, y)
	if got := canonical(cmpTerm("eq", sum, constTerm(1, 32))); got.kind != termCmp {
		t.Fatalf("non-Boolean comparison was rewritten: %s", got)
	}
}

// A byte-sized status assembled by conditional assignments is tested arm by
// arm. This is the source shape of `st == 0` after several fail-closed checks;
// leaving the complete status tree under one comparison makes a caller's
// post-loop result need a much larger diagram than the equivalent machine CFG.
func TestCanonicalSmallConditionalComparison(t *testing.T) {
	c, d := paramTerm("c", 1), paramTerm("d", 1)
	status := iteTerm(c, constTerm(4, 8), iteTerm(d, constTerm(5, 8), constTerm(0, 8)))
	for _, code := range []string{"eq", "ne"} {
		for _, want := range []uint64{0, 4, 5, 7} {
			original := cmpTerm(code, status, constTerm(want, 8))
			normalized := canonical(original)
			narrowed := canonical(truncate(original, 1))
			if narrowed.width != 1 {
				t.Fatalf("%s %d after one-bit truncation has width %d: %s", code, want, narrowed.width, narrowed)
			}
			for cv := uint64(0); cv < 2; cv++ {
				for dv := uint64(0); dv < 2; dv++ {
					inputs := map[string]uint64{"c": cv, "d": dv}
					if got, expected := normalized.eval(inputs), original.eval(inputs); got != expected {
						t.Fatalf("%s %d at c=%d d=%d: got %d, want %d (%s)", code, want, cv, dv, got, expected, normalized)
					}
					if got, expected := narrowed.eval(inputs), original.eval(inputs)&1; got != expected {
						t.Fatalf("narrowed %s %d at c=%d d=%d: got %d, want %d (%s)", code, want, cv, dv, got, expected, narrowed)
					}
				}
			}
			var comparisonStillWrapsConditional func(*term) bool
			comparisonStillWrapsConditional = func(term *term) bool {
				if term == nil {
					return false
				}
				if term.kind == termCmp && (term.left.kind == termIte || term.right.kind == termIte) {
					return true
				}
				return comparisonStillWrapsConditional(term.cond) || comparisonStillWrapsConditional(term.left) || comparisonStillWrapsConditional(term.right)
			}
			if comparisonStillWrapsConditional(normalized) {
				t.Fatalf("%s %d still wraps a conditional: %s", code, want, normalized)
			}
			var hasConditional func(*term) bool
			hasConditional = func(term *term) bool {
				return term != nil && (term.kind == termIte || hasConditional(term.cond) || hasConditional(term.left) || hasConditional(term.right))
			}
			if hasConditional(normalized) {
				t.Fatalf("%s %d retained a boolean conditional: %s", code, want, normalized)
			}
		}
	}
	count := paramTerm("count", 16)
	updated := iteTerm(c, binaryTerm("sub", count, constTerm(1, 16)), count)
	var comparisonStillWrapsConditional func(*term) bool
	comparisonStillWrapsConditional = func(term *term) bool {
		if term == nil {
			return false
		}
		if term.kind == termCmp && (term.left.kind == termIte || term.right.kind == termIte) {
			return true
		}
		return comparisonStillWrapsConditional(term.cond) || comparisonStillWrapsConditional(term.left) || comparisonStillWrapsConditional(term.right)
	}
	for _, code := range []string{"eq", "ne"} {
		original := cmpTerm(code, updated, constTerm(0, 16))
		normalized := canonical(original)
		for cv := uint64(0); cv < 2; cv++ {
			for _, value := range []uint64{0, 1, 2, 0xffff} {
				inputs := map[string]uint64{"c": cv, "count": value}
				if got, expected := normalized.eval(inputs), original.eval(inputs); got != expected {
					t.Fatalf("u16 %s at c=%d count=%d: got %d, want %d (%s)", code, cv, value, got, expected, normalized)
				}
			}
		}
		if comparisonStillWrapsConditional(normalized) {
			t.Fatalf("u16 %s still wraps a conditional: %s", code, normalized)
		}
	}
	if got := canonical(cmpTerm("lo", status, constTerm(4, 8))); got.kind != termCmp {
		t.Fatalf("ordered conditional comparison was distributed: %s", got)
	}
}

// Ordered fail-closed updates repeatedly test the prior status for zero. Once
// comparisons distribute over the status tree, the new Boolean formula must
// itself canonicalize: the final status is zero exactly when no check fired.
func TestCanonicalOrderedStatusZero(t *testing.T) {
	fail4, fail5a, fail5b := paramTerm("fail4", 1), paramTerm("fail5a", 1), paramTerm("fail5b", 1)
	status := iteTerm(fail4, constTerm(4, 8), constTerm(0, 8))
	status = iteTerm(binaryTerm("and", truncate(cmpTerm("eq", status, constTerm(0, 8)), 1), fail5a), constTerm(5, 8), status)
	status = iteTerm(binaryTerm("and", truncate(cmpTerm("eq", status, constTerm(0, 8)), 1), fail5b), constTerm(5, 8), status)
	zero := canonical(truncate(cmpTerm("eq", status, constTerm(0, 8)), 1))
	want := canonical(binaryTerm("and", notTerm(fail4), binaryTerm("and", notTerm(fail5a), notTerm(fail5b))))
	parts := logicalConjuncts(zero)
	wantParts := []*term{notTerm(fail4), notTerm(fail5a), notTerm(fail5b)}
	if zero.width != 1 || len(parts) != len(wantParts) {
		t.Fatalf("ordered status zero has %d factors: %s", len(parts), zero)
	}
	for i := range parts {
		if !equalTerms(parts[i], wantParts[i]) {
			t.Fatalf("ordered status factor %d: %s, want %s (whole %s)", i, parts[i], wantParts[i], zero)
		}
	}
	for f4 := uint64(0); f4 < 2; f4++ {
		for f5a := uint64(0); f5a < 2; f5a++ {
			for f5b := uint64(0); f5b < 2; f5b++ {
				inputs := map[string]uint64{"fail4": f4, "fail5a": f5a, "fail5b": f5b}
				if got, expected := zero.eval(inputs), want.eval(inputs); got != expected {
					t.Fatalf("at %v: got %d, want %d", inputs, got, expected)
				}
			}
		}
	}
}

// Constant-valued decision trees need not make their choices in the same
// order. Equality follows when the predicate selecting each possible result is
// equivalent; a changed leaf is still refuted, and non-finite shapes do not
// enter this theorem.
func TestImpliesFiniteConditionalEqual(t *testing.T) {
	c, d := paramTerm("c", 1), paramTerm("d", 1)
	left := iteTerm(c, constTerm(4, 8), iteTerm(d, constTerm(5, 8), constTerm(0, 8)))
	right := iteTerm(d, iteTerm(c, constTerm(4, 8), constTerm(5, 8)), iteTerm(c, constTerm(4, 8), constTerm(0, 8)))
	widthOf := func(string) int { return 1 }
	if holds, decided, applicable := impliesFiniteConditionalEqual(constTerm(1, 1), left, right, widthOf, nil); !applicable || !decided || !holds {
		t.Fatalf("reordered decision trees: applicable=%v decided=%v holds=%v", applicable, decided, holds)
	}
	different := iteTerm(d, iteTerm(c, constTerm(3, 8), constTerm(5, 8)), iteTerm(c, constTerm(4, 8), constTerm(0, 8)))
	if holds, decided, applicable := impliesFiniteConditionalEqual(constTerm(1, 1), left, different, widthOf, nil); !applicable || !decided || holds {
		t.Fatalf("changed leaf: applicable=%v decided=%v holds=%v", applicable, decided, holds)
	}
	x := paramTerm("x", 8)
	booleanLeaf := iteTerm(c, cmpTerm("eq", x, constTerm(0, 8)), constTerm(5, 8))
	if holds, decided, applicable := impliesFiniteConditionalEqual(constTerm(1, 1), booleanLeaf, booleanLeaf, widthOf, nil); !applicable || !decided || !holds {
		t.Fatalf("symbolic Boolean leaf: applicable=%v decided=%v holds=%v", applicable, decided, holds)
	}
	withParameter := iteTerm(c, paramTerm("value", 8), constTerm(0, 8))
	if _, _, applicable := impliesFiniteConditionalEqual(constTerm(1, 1), left, withParameter, widthOf, nil); applicable {
		t.Fatal("a nonconstant leaf entered the finite-result theorem")
	}
	wide := iteTerm(c, constTerm(1, 16), constTerm(0, 16))
	if _, _, applicable := impliesFiniteConditionalEqual(constTerm(1, 1), wide, wide, widthOf, nil); applicable {
		t.Fatal("a wide result entered the finite-result theorem")
	}
}

// Conjuncts of a case premise settle matching and complementary branch
// conditions structurally before the pruning BDD is needed. Compound Boolean
// conditions use only facts the premise supplies.
func TestPruneUnderStructuralConjuncts(t *testing.T) {
	a, b := paramTerm("a", 1), paramTerm("b", 1)
	x, y, z := paramTerm("x", 32), paramTerm("y", 32), paramTerm("z", 32)
	premise := binaryTerm("and", a, notTerm(b))
	value := iteTerm(binaryTerm("and", a, b), x, iteTerm(a, iteTerm(b, x, y), z))
	widthOf := func(string) int { return 32 }
	got := pruneUnder(premise, []*term{value}, widthOf)[0]
	if !equalTerms(got, y) {
		t.Fatalf("pruned nested value: %s, want %s", got, y)
	}
	unknown := iteTerm(paramTerm("c", 1), x, y)
	if got := pruneUnder(premise, []*term{unknown}, widthOf)[0]; got.kind != termIte {
		t.Fatalf("a condition absent from the premise was settled: %s", got)
	}
	wideBool := binaryTerm("and", cmpTerm("eq", paramTerm("w", 32), constTerm(0, 32)), constTerm(1, 32))
	if got := pruneUnder(premise, []*term{iteTerm(wideBool, x, y)}, widthOf)[0]; got.kind != termIte {
		t.Fatalf("an unrelated wider Boolean condition was settled: %s", got)
	}
}

// Zero/nonzero facts may differ only by a redundant narrow-register mask.
// Match those facts without rewriting the terms, but reject a mask that can
// actually clear a set bit.
func TestPruneUnderRedundantLowMaskFact(t *testing.T) {
	x := paramTerm("x", 64)
	masked := binaryTerm("and", x, constTerm(0x3fff, 64))
	narrowView := truncate(masked, 16)
	wideNonzero := truncate(cmpTerm("ne", masked, constTerm(0, 64)), 1)
	narrowNonzero := truncate(cmpTerm("ne", narrowView, constTerm(0, 16)), 1)

	if relation := maskedZeroTestRelation(canonical(wideNonzero), canonical(narrowNonzero)); relation != 1 {
		t.Fatalf("same zero test relation = %d, want 1", relation)
	}
	wideZero := truncate(cmpTerm("eq", masked, constTerm(0, 64)), 1)
	if relation := maskedZeroTestRelation(canonical(wideZero), canonical(narrowNonzero)); relation != -1 {
		t.Fatalf("opposite zero test relation = %d, want -1", relation)
	}

	left, right := paramTerm("left", 32), paramTerm("right", 32)
	widthOf := func(string) int { return 64 }
	if got := pruneUnder(narrowNonzero, []*term{iteTerm(wideNonzero, left, right)}, widthOf)[0]; !equalTerms(got, left) {
		t.Fatalf("matching masked fact selected %s, want %s", got, left)
	}
	if got := pruneUnder(narrowNonzero, []*term{iteTerm(wideZero, left, right)}, widthOf)[0]; !equalTerms(got, right) {
		t.Fatalf("opposite masked fact selected %s, want %s", got, right)
	}

	lowByteNonzero := truncate(cmpTerm("ne", truncate(masked, 8), constTerm(0, 8)), 1)
	if relation := maskedZeroTestRelation(canonical(wideNonzero), canonical(lowByteNonzero)); relation != 0 {
		t.Fatalf("value-changing mask relation = %d, want 0", relation)
	}
	if got := pruneUnder(wideNonzero, []*term{iteTerm(lowByteNonzero, left, right)}, widthOf)[0]; got.kind != termIte {
		t.Fatalf("value-changing mask settled the branch: %s", got)
	}

	for xv := uint64(0); xv <= 0xffff; xv++ {
		inputs := map[string]uint64{"x": xv}
		if got, want := wideNonzero.eval(inputs), narrowNonzero.eval(inputs); got != want {
			t.Fatalf("x=%#x: wide predicate %d, narrow predicate %d", xv, got, want)
		}
	}
}

// Structural premise facts simplify complete Boolean formulas, not only ITE
// conditions. AND/OR short-circuit before a large unrelated tail is visited.
func TestPruneUnderBooleanFormula(t *testing.T) {
	p := paramTerm("p", 1)
	unknown := truncate(cmpTerm("eq", selectTerm("s.pages", paramTerm("i", 32), 64), constTerm(7, 64)), 1)
	widthOf := func(string) int { return 64 }

	falseFormula := binaryTerm("and", notTerm(p), unknown)
	if got := pruneUnder(p, []*term{falseFormula}, widthOf)[0]; got.kind != termConst || got.value != 0 {
		t.Fatalf("known-false formula pruned to %s", got)
	}
	trueFormula := binaryTerm("or", p, unknown)
	if got := pruneUnder(p, []*term{trueFormula}, widthOf)[0]; got.kind != termConst || got.value != 1 {
		t.Fatalf("known-true formula pruned to %s", got)
	}
	undecided := binaryTerm("and", p, unknown)
	if got := pruneUnder(p, []*term{undecided}, widthOf)[0]; got.kind == termConst {
		t.Fatalf("unknown formula was decided: %s", got)
	}
}

// Direct premise facts remain useful when the premise as a whole contains a
// construct the branch-pruning diagram cannot handle cheaply. The fact-only
// pass removes the redundant guard and leaves an unrelated guard untouched.
func TestImpliesEqualUsesStructuralFactsBeforeDiagram(t *testing.T) {
	p, q := paramTerm("p", 1), paramTerm("q", 1)
	bound := paramTerm("bound", 8)
	k := paramTerm("k@q", 8)
	quantified := quantTerm("forall", "k@q", 8, cmpTerm("ls", k, bound), k)
	premise := binaryTerm("and", p, quantified)
	widthOf := func(string) int { return 8 }

	if holds, decided := impliesEqual(premise, binaryTerm("and", p, q), q, widthOf); !decided || !holds {
		t.Fatalf("direct fact must settle guarded equality: holds=%v decided=%v", holds, decided)
	}
	if got := canonical(pruneUnderFacts(premise, []*term{binaryTerm("and", p, notTerm(q))})[0]); got.kind == termConst {
		t.Fatalf("unrelated fact was decided: %s", got)
	}
	x := paramTerm("x", 8)
	wideZero := cmpTerm("eq", x, constTerm(0, 8))
	wideNonzero := truncate(cmpTerm("ne", x, constTerm(0, 8)), 1)
	if got := pruneUnderFacts(wideNonzero, []*term{wideZero})[0]; got.kind != termConst || got.width != 8 || got.value != 0 {
		t.Fatalf("wide Boolean fact pruned to %s, want u8(0)", got)
	}
	if got := pruneUnderFacts(wideNonzero, []*term{x})[0]; got.kind != termParam {
		t.Fatalf("non-Boolean wide value was decided: %s", got)
	}
}

// Pure scalar status checks can be split into separate post-loop reach facts;
// a factor reading symbolic memory stays atomic so a callee's memory condition
// is not duplicated through every postcondition.
func TestRefinePureReachFactors(t *testing.T) {
	a, b := paramTerm("a", 1), paramTerm("b", 1)
	status := iteTerm(a, constTerm(4, 8), iteTerm(b, constTerm(5, 8), constTerm(0, 8)))
	zero := truncate(cmpTerm("eq", status, constTerm(0, 8)), 1)
	if got := refinePureReachFactors([]*term{zero}); len(got) != 2 {
		t.Fatalf("pure status factor split into %d parts, want 2: %v", len(got), got)
	}
	combinedStatus := iteTerm(binaryTerm("or", a, b), constTerm(4, 8), constTerm(0, 8))
	combinedZero := truncate(cmpTerm("eq", combinedStatus, constTerm(0, 8)), 1)
	combined := refinePureReachFactors([]*term{combinedZero})
	if len(combined) != 2 || !equalTerms(combined[0], notTerm(a)) || !equalTerms(combined[1], notTerm(b)) {
		t.Fatalf("negated disjunction factors: %v", combined)
	}
	x, y := paramTerm("x", 64), paramTerm("y", 64)
	wideA := cmpTerm("ne", binaryTerm("and", x, constTerm(15, 64)), constTerm(0, 64))
	wideB := cmpTerm("ne", binaryTerm("and", y, constTerm(15, 64)), constTerm(0, 64))
	wideStatus := iteTerm(binaryTerm("or", wideA, wideB), constTerm(4, 8), constTerm(0, 8))
	wideZero := truncate(cmpTerm("eq", wideStatus, constTerm(0, 8)), 1)
	wide := refinePureReachFactors([]*term{wideZero})
	if len(wide) != 2 {
		t.Fatalf("wide Boolean disjunction factors: %v", wide)
	}
	for xv := uint64(0); xv < 18; xv++ {
		for yv := uint64(0); yv < 18; yv++ {
			inputs := map[string]uint64{"x": xv, "y": yv}
			if got, want := wide[0].eval(inputs), notTerm(truncate(wideA, 1)).eval(inputs); got != want {
				t.Fatalf("wide factor 0 at %v: got %d, want %d", inputs, got, want)
			}
			if got, want := wide[1].eval(inputs), notTerm(truncate(wideB, 1)).eval(inputs); got != want {
				t.Fatalf("wide factor 1 at %v: got %d, want %d", inputs, got, want)
			}
		}
	}
	c := paramTerm("c", 1)
	outer := binaryTerm("and", canonical(wideZero), notTerm(c))
	if got := refinePureReachFactors([]*term{outer}); len(got) != 3 {
		t.Fatalf("nested negated disjunction split into %d factors, want 3: %v", len(got), got)
	}
	memoryBad := truncate(cmpTerm("ne", selectTerm("s.pages", paramTerm("i", 32), 8), constTerm(0, 8)), 1)
	memoryStatus := iteTerm(memoryBad, constTerm(4, 8), iteTerm(b, constTerm(5, 8), constTerm(0, 8)))
	memoryZero := truncate(cmpTerm("eq", memoryStatus, constTerm(0, 8)), 1)
	if got := refinePureReachFactors([]*term{memoryZero}); len(got) != 1 || !equalTerms(got[0], memoryZero) {
		t.Fatalf("memory-dependent factor was expanded: %v", got)
	}
}

// Later reach factors are interpreted under the prefix accumulated before
// them. Removing a repeated prefix fact preserves both resulting partitions
// and leaves unrelated memory conditions intact.
func TestRefineReachFactorUnderPrefix(t *testing.T) {
	p, q := paramTerm("p", 1), paramTerm("q", 1)
	factor := binaryTerm("and", p, q)
	refined := refineReachFactorUnder(p, factor)
	if !equalTerms(refined, q) {
		t.Fatalf("factor refined to %s, want %s", refined, q)
	}
	for pv := uint64(0); pv < 2; pv++ {
		for qv := uint64(0); qv < 2; qv++ {
			env := map[string]uint64{"p": pv, "q": qv}
			for _, pair := range [][2]*term{
				{binaryTerm("and", p, factor), binaryTerm("and", p, refined)},
				{binaryTerm("and", p, notTerm(factor)), binaryTerm("and", p, notTerm(refined))},
			} {
				if got, want := pair[1].eval(env), pair[0].eval(env); got != want {
					t.Fatalf("partition changed at %v: got %d, want %d", env, got, want)
				}
			}
		}
	}
	memory := truncate(cmpTerm("ne", selectTerm("s.pages", paramTerm("i", 32), 64), constTerm(0, 64)), 1)
	if got := refineReachFactorUnder(p, memory); !equalTerms(got, memory) {
		t.Fatalf("unrelated memory factor changed to %s", got)
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

// A known one-bit value remains Boolean through a wider register truncation.
// Its zero test should expose the bit instead of leaving a comparison around
// the full-mask wrapper.
func TestCanonicalZeroTestOfKnownBit(t *testing.T) {
	x := paramTerm("x", 64)
	bit := binaryTerm("and", x, constTerm(1, 64))
	word := truncate(bit, 32)
	for _, code := range []string{"eq", "ne"} {
		machine := truncate(cmpTerm(code, word, constTerm(0, 32)), 1)
		want := truncate(bit, 1)
		if code == "eq" {
			want = notTerm(want)
		}
		got, want := canonical(machine), canonical(want)
		if !equalTerms(got, want) {
			t.Fatalf("%s zero test: %s, want %s", code, got, want)
		}
		for xv := uint64(0); xv < 256; xv++ {
			inputs := map[string]uint64{"x": xv}
			if actual, expected := got.eval(inputs), machine.eval(inputs); actual != expected {
				t.Fatalf("%s x=%d: got %d, want %d", code, xv, actual, expected)
			}
		}
	}

	twoBits := truncate(binaryTerm("and", x, constTerm(3, 64)), 32)
	if got := canonical(truncate(cmpTerm("eq", twoBits, constTerm(0, 32)), 1)); got.kind != termCmp {
		t.Fatalf("two-bit zero test was reduced as Boolean: %s", got)
	}
}
