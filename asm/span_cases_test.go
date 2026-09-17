package asm

import (
	"strings"
	"testing"
)

// canonicalLinear respells the two sides' spellings of one value as one
// term: nested constant masks across widths (a truncation then a u16
// narrowing on the machine, a u16 narrowing then an extension on the Oak
// side) fold to one mask over the innermost operand; a linear subterm is
// written out in its normal form; an equality of two terms with one form
// is its constant.
func TestCanonicalLinearRespellsMasksAndForms(t *testing.T) {
	x := paramTerm("x", 64)
	shifted := binaryTerm("shr", x, constTerm(14, 64))
	// Machine: (x >> 14) truncated to 32 bits, then `and 65535` at 32.
	machine := &term{kind: termBinary, width: 32, op: "and", left: truncate(shifted, 32), right: constTerm(65535, 32)}
	// Oak: (x >> 14) narrowed to u16, then widened to u32.
	oak := zeroExtend(&term{kind: termBinary, width: 16, op: "and", left: shifted, right: constTerm(65535, 16)}, 32)
	memo := map[*term]*term{}
	a, b := canonicalLinear(machine, memo), canonicalLinear(oak, memo)
	if !equalTerms(a, b) {
		t.Fatalf("nested masks must fold to one term:\n  machine %s\n  oak     %s", a, b)
	}
	if a.kind != termBinary || a.op != "and" || a.right.kind != termConst || a.right.value != 65535 || a.left != shifted {
		t.Fatalf("the fold keeps the innermost operand under one mask: %s", a)
	}
	for _, env := range []map[string]uint64{{"x": 0}, {"x": 0xFFFFFFFFFFFFFFFF}, {"x": 0x123456789ABCDEF}, {"x": 1 << 30}} {
		if machine.eval(env) != a.eval(env) || oak.eval(env) != b.eval(env) {
			t.Fatalf("the respelling must keep the value at x=%d", env["x"])
		}
	}

	// A linear index in two spellings is one written-out form, and an
	// equality of the two is true.
	dom, i, tbl := paramTerm("dom", 32), paramTerm("i", 32), paramTerm("t", 16)
	oakIndex := binaryTerm("add", binaryTerm("mul", constTerm(512, 32), dom), binaryTerm("add", binaryTerm("mul", zeroExtend(tbl, 32), constTerm(128, 32)), i))
	asmIndex := binaryTerm("add", binaryTerm("shl", zeroExtend(tbl, 32), constTerm(7, 32)), binaryTerm("add", i, binaryTerm("shl", dom, constTerm(9, 32))))
	memo = map[*term]*term{}
	if l, r := canonicalLinear(oakIndex, memo), canonicalLinear(asmIndex, memo); !equalTerms(l, r) {
		t.Fatalf("one form, one spelling:\n  %s\n  %s", l, r)
	}
	if eq := canonicalLinear(cmpTerm("eq", oakIndex, asmIndex), map[*term]*term{}); eq.kind != termConst || eq.value != 1 {
		t.Fatalf("an equality of one form is true: %s", eq)
	}
	if ne := canonicalLinear(cmpTerm("ne", oakIndex, binaryTerm("add", asmIndex, constTerm(1, 32))), map[*term]*term{}); ne.kind == termConst {
		t.Fatalf("different forms are not decided by spelling: %s", ne)
	}
	if reads := canonicalLinear(selectTerm("s.pages", oakIndex, 64), memo); !equalTerms(reads, canonicalLinear(selectTerm("s.pages", asmIndex, 64), memo)) {
		t.Fatalf("a read's index is respelled too: %s", reads)
	}
	// A comparison of two constants is its value, and an equality whose
	// sides are one term structurally — an index outside the linear form,
	// `(ipa shr 25) and 1` — is true.
	entry := &term{kind: termCmp, width: 1, op: "lo", left: constTerm(0, 32), right: constTerm(128, 32)}
	if c := canonicalLinear(entry, map[*term]*term{}); c.kind != termConst || c.value != 1 {
		t.Fatalf("0 lo 128 is 1: %s", c)
	}
	// A mask covering every bit a comparison can have set is the identity,
	// whichever side the constant is on; a u16 call result read with its
	// unspecified upper half, `(r and 65535) or (hi shl 16)`, under `and
	// 65535` is `r and 65535`.
	cmp := cmpTerm("eq", paramTerm("a", 32), paramTerm("b", 32))
	if c := canonicalLinear(&term{kind: termBinary, width: 1, op: "and", left: constTerm(1, 1), right: cmp}, map[*term]*term{}); !equalTerms(c, truncate(cmp, 1)) {
		t.Fatalf("1 and c is c: %s", c)
	}
	r, hi := paramTerm("call1", 32), paramTerm("call1#hi", 32)
	read := binaryTerm("and", binaryTerm("or", binaryTerm("and", r, constTerm(65535, 32)), binaryTerm("shl", hi, constTerm(16, 32))), constTerm(65535, 32))
	if c := canonicalLinear(read, map[*term]*term{}); !equalTerms(c, binaryTerm("and", r, constTerm(65535, 32))) {
		t.Fatalf("the unspecified upper half strips under the mask: %s", c)
	}
	odd := binaryTerm("and", binaryTerm("shr", paramTerm("ipa", 64), constTerm(25, 64)), constTerm(1, 64))
	same := &term{kind: termCmp, width: 1, op: "eq", left: binaryTerm("add", zeroExtend(dom, 64), odd), right: binaryTerm("add", zeroExtend(dom, 64), odd)}
	if c := canonicalLinear(same, map[*term]*term{}); c.kind != termConst || c.value != 1 {
		t.Fatalf("X eq X is 1 even outside the linear form: %s", c)
	}
}

// spanEqualByCases: the machine writes a constant per permission case,
// the Oak side one value with the permission's conditionals inside; under
// each case both prune to one term.
func TestSpanEqualByCasesSplitsOnSmallComparisons(t *testing.T) {
	perm, at, pa := paramTerm("perm", 8), paramTerm("s.pages?", 32), paramTerm("pa", 64)
	entry := selectTerm("s.pages", at, 64)
	index := paramTerm("leaf", 32)
	hit := cmpTerm("eq", at, index)
	rw, rx := cmpTerm("eq", perm, constTerm(1, 8)), cmpTerm("eq", perm, constTerm(2, 8))
	ap := binaryTerm("shl", iteTerm(rw, constTerm(1, 64), constTerm(3, 64)), constTerm(6, 64))
	xn := iteTerm(rx, constTerm(1<<53, 64), constTerm(1<<53|1<<54, 64))
	oakValue := binaryTerm("or", binaryTerm("or", pa, ap), xn)
	oak := iteTerm(hit, oakValue, entry)
	branch := func(cond *term, apBits, xnBits uint64) (*term, *term) {
		return binaryTerm("and", cond, hit), binaryTerm("or", binaryTerm("or", pa, constTerm(apBits, 64)), constTerm(xnBits, 64))
	}
	not := func(c *term) *term { return binaryTerm("xor", c, constTerm(1, 1)) }
	c1, v1 := branch(binaryTerm("and", rx, rw), 64, 1<<53)
	c2, v2 := branch(binaryTerm("and", not(rx), rw), 64, 1<<53|1<<54)
	c3, v3 := branch(binaryTerm("and", rx, not(rw)), 192, 1<<53)
	c4, v4 := branch(binaryTerm("and", not(rx), not(rw)), 192, 1<<53|1<<54)
	machine := iteTerm(c1, v1, iteTerm(c2, v2, iteTerm(c3, v3, iteTerm(c4, v4, entry))))
	premise := cmpTerm("lo", paramTerm("va", 64), constTerm(1<<32, 64))
	equal, decided := spanEqualByCases("map_page", "s.pages", premise, oak, machine, nil)
	if !decided || !equal {
		t.Fatalf("the four permission cases must close: equal=%v decided=%v", equal, decided)
	}
	// A machine that writes the wrong bits in one case is not proven.
	_, v3wrong := branch(binaryTerm("and", rx, not(rw)), 64, 1<<53)
	wrong := iteTerm(c1, v1, iteTerm(c2, v2, iteTerm(c3, v3wrong, iteTerm(c4, v4, entry))))
	if _, decided := spanEqualByCases("map_page", "s.pages", premise, oak, wrong, nil); decided {
		t.Fatal("a case that is not one term must stay undecided")
	}
	conds := spanSplitConditions(premise, []*term{oak, machine}, spanCaseSplitLimit)
	if len(conds) < 2 || !strings.Contains(conds[0].String(), "perm eq 1") || !strings.Contains(conds[1].String(), "perm eq 2") {
		t.Fatalf("the split is over the permission tests: %v", conds)
	}
	for _, c := range conds {
		if readsMemory(c) {
			t.Fatalf("a condition over a memory read is never split on: %s", c)
		}
	}
	// A comparison that is a constant once respelled is not a case.
	folded := cmpTerm("eq", binaryTerm("and", constTerm(0, 8), constTerm(255, 8)), constTerm(0, 8))
	for _, c := range spanSplitConditions(premise, []*term{iteTerm(folded, oak, machine)}, spanCaseSplitLimit) {
		if c == folded || canonicalLinear(c, map[*term]*term{}).kind == termConst {
			t.Fatalf("a constant comparison must not be split on: %s", c)
		}
	}
}
