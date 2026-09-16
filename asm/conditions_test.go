package asm

import "testing"

// conjoin and disjoin fold what the paths' conditions produce at the
// joins and in the guards past them: constants, a condition against its
// complement, and a conjunct or disjunct the other side already holds.
func TestConjoinDisjoinFold(t *testing.T) {
	x := paramTerm("x", 32)
	// One-bit conditions, as the guards are (a comparison carries its
	// operands' width until truncated).
	ge := truncate(cmpTerm("hs", x, constTerm(16384, 32)), 1)
	lo := truncate(cmpTerm("lo", x, constTerm(16384, 32)), 1)
	eq0 := truncate(cmpTerm("eq", paramTerm("y", 32), constTerm(0, 32)), 1)
	one, zero := constTerm(1, 1), constTerm(0, 1)

	if got := conjoin(ge, lo); got.kind != termConst || got.value != 0 {
		t.Errorf("ge and lo of the same operands must fold to false, got %s", got)
	}
	if got := disjoin(ge, lo); got.kind != termConst || got.value != 1 {
		t.Errorf("ge or lo of the same operands must fold to true, got %s", got)
	}
	if got := disjoin(eq0, notTerm(eq0)); got.kind != termConst || got.value != 1 {
		t.Errorf("c or not c must fold to true, got %s", got)
	}
	if got := conjoin(ge, one); got != ge {
		t.Errorf("a conjunct of true drops out, got %s", got)
	}
	if got := conjoin(ge, zero); got.kind != termConst || got.value != 0 {
		t.Errorf("a conjunct of false decides, got %s", got)
	}
	if got := disjoin(zero, ge); got != ge {
		t.Errorf("a disjunct of false drops out, got %s", got)
	}
	both := conjoin(ge, eq0)
	if got := conjoin(both, ge); got != both {
		t.Errorf("a conjunct already held is absorbed: (ge and eq0) and ge must be (ge and eq0), got %s", got)
	}
	if got := conjoin(ge, both); got != both {
		t.Errorf("absorption either way round, got %s", got)
	}
	if got := disjoin(disjoin(ge, eq0), eq0); got.kind != termBinary || got.op != "or" || got.left != ge || got.right != eq0 {
		t.Errorf("a disjunct already held is absorbed, got %s", got)
	}
	if got := conjoin(nil, ge); got != ge {
		t.Errorf("nil is true for conjoin, got %s", got)
	}
}
