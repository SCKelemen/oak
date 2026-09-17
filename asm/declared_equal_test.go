package asm

import "testing"

// A summarized hash consumes the same byte through narrow machine loads
// and widened Oak parameters. Its shared arithmetic DAG should not need
// a bit-level diagram just to establish those leaf equalities.
func TestImpliesEqualDeclaredByteViewsInSharedDAG(t *testing.T) {
	build := func(wide bool) *term {
		byteView := paramTerm("byte", 8)
		if wide {
			byteView = zeroExtend(byteView, 32)
		}
		x := &term{kind: termBinary, width: 32, op: "and", left: byteView, right: constTerm(255, 32)}
		y := paramTerm("seed", 32)
		for k := 0; k < 24; k++ {
			x = binaryTerm("add", x, y)
			y = binaryTerm("xor", y, binaryTerm("or", binaryTerm("shl", x, constTerm(13, 32)), binaryTerm("shr", x, constTerm(19, 32))))
		}
		return binaryTerm("xor", x, y)
	}
	a, b := build(true), build(false)
	widthOf := func(name string) int {
		if name == "byte" {
			return 8
		}
		return 32
	}
	budget := &nodeBudget{remaining: 2000, loop: true}
	if holds, decided := impliesEqualWithin(constTerm(1, 1), a, b, widthOf, budget); !decided || !holds {
		t.Fatalf("same byte views must prove within the small budget: holds=%v decided=%v remaining=%d", holds, decided, budget.remaining)
	}
	if holds, decided := impliesEqual(constTerm(1, 1), a, binaryTerm("xor", b, constTerm(1, 32)), widthOf); !decided || holds {
		t.Fatalf("a changed output bit must be refuted: holds=%v decided=%v", holds, decided)
	}
}

func TestDeclaredEqualityKeepsWidthSensitiveOperations(t *testing.T) {
	byteView, wideView := paramTerm("byte", 8), zeroExtend(paramTerm("byte", 8), 32)
	widthOf := func(string) int { return 8 }
	// At 0x80 the signed byte is negative and its widened value positive.
	cmp8, cmp32 := cmpTerm("lt", byteView, constTerm(0, 8)), cmpTerm("lt", wideView, constTerm(0, 32))
	if holds, decided := impliesEqual(constTerm(1, 1), cmp8, cmp32, widthOf); !decided || holds {
		t.Fatalf("signed comparison widths must remain distinct: holds=%v decided=%v", holds, decided)
	}
	// A declared u32 narrowed to a byte has discarded observable bits.
	full := paramTerm("full", 32)
	if holds, decided := impliesEqual(constTerm(1, 1), full, truncate(full, 8), func(string) int { return 32 }); !decided || holds {
		t.Fatalf("truncated high bits must remain distinct: holds=%v decided=%v", holds, decided)
	}
}

func TestEqualTermsAtDeclaredWidths(t *testing.T) {
	byteView := paramTerm("byte", 8)
	wideView := zeroExtend(byteView, 32)
	for _, declared := range []int{0, 8, 16, 32, 65} {
		got := equalTermsAtDeclaredWidths(byteView, wideView, func(string) int { return declared })
		if got != (declared == 8) {
			t.Fatalf("declared width %d: equality=%v", declared, got)
		}
	}
	if equalTermsAtDeclaredWidths(byteView, wideView, nil) {
		t.Fatal("a width relaxation requires a declaration")
	}
	if equalTermsAtDeclaredWidths(byteView, paramTerm("other", 8), func(string) int { return 8 }) {
		t.Fatal("different symbols must remain distinct")
	}
	float32 := &term{kind: termFloat, width: 64, op: "fcvt", left: wideView}
	float64 := &term{kind: termFloat, width: 64, op: "fcvt", left: zeroExtend(byteView, 64)}
	if equalTermsAtDeclaredWidths(float32, float64, func(string) int { return 8 }) {
		t.Fatal("float input widths determine the interpretation")
	}
	if float32.eval(map[string]uint64{"byte": 128}) == float64.eval(map[string]uint64{"byte": 128}) {
		t.Fatal("the float regression must use different interpretations")
	}
	quantifier := func(view *term) *term {
		masked := &term{kind: termBinary, width: 32, op: "and", left: view, right: constTerm(511, 32)}
		return &term{kind: termQuant, width: 1, name: "byte", op: "exists", value: 9, left: cmpTerm("eq", masked, constTerm(256, 32))}
	}
	qa, qb := quantifier(byteView), quantifier(wideView)
	if equalTermsAtDeclaredWidths(qa, qb, func(string) int { return 8 }) {
		t.Fatal("the quantifier's bound name shadows the external declaration")
	}
	if qa.eval(map[string]uint64{}) == qb.eval(map[string]uint64{}) {
		t.Fatal("the quantifier regression must distinguish the discarded bit")
	}
}
