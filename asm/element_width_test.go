package asm

import "testing"

// A byte element read at a widened width (the machine's `ldrb` into a
// word) and at its own (the Oak body's u8) is one element: its fixed-
// memory value is the declared width's, so two spellings of the same
// selection — the Oak conditional over the lane and the machine's over
// the lane masked — agree on every valuation and are proven equal. (The
// evaluator once read the element at the use width and refuted them.)
func TestElementParameterKeepsItsDeclaredWidth(t *testing.T) {
	l := paramTerm("loop1.l", 32)
	var mux *term = paramTerm("cand[15]", 8)
	for k := 14; k >= 0; k-- {
		mux = iteTerm(cmpTerm("eq", l, constTerm(uint64(k), 32)), paramTerm(spanElemName("cand", int64(k)), 8), mux)
	}
	h1, h2 := paramTerm("loop1.hits", 32), paramTerm("loop2.hits", 32)
	oak := zeroExtend(iteTerm(cmpTerm("ne", mux, constTerm(0, 8)), h2, h1), 64)
	asmCond := binaryTerm("xor", truncate(cmpTerm("eq", binaryTerm("and", zeroExtend(mux, 32), constTerm(255, 32)), constTerm(0, 32)), 1), constTerm(1, 1))
	asm := binaryTerm("and", iteTerm(asmCond, paramTerm("loop2.hits", 64), paramTerm("loop1.hits", 64)), constTerm(mask(32), 64))
	if wide := zeroExtend(paramTerm("cand[3]", 8), 32); wide.declaredWidth() != 8 || wide.eval(nil) != paramTerm("cand[3]", 8).eval(nil) {
		t.Fatalf("a widened element must read its declared width's value: %d vs %d", wide.eval(nil), paramTerm("cand[3]", 8).eval(nil))
	}
	widthOf := func(name string) int {
		if name == "loop1.l" || name == "loop1.hits" || name == "loop2.hits" {
			return 32
		}
		return 8
	}
	holds, decided := impliesEqual(cmpTerm("ls", l, constTerm(16, 32)), oak, asm, widthOf)
	if !decided || !holds {
		t.Fatalf("the two spellings must be proven equal: holds=%v decided=%v", holds, decided)
	}
}
