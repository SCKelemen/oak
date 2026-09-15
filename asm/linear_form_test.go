package asm

import "testing"

// The linear normal form sees through a low mask that covers the operand's
// known bits: `u64(index)` over a u16 parameter (`index and 0xFFFF` on the
// Oak side, `and w1, w1, #65535` read at 64 bits on the machine's) is the
// parameter, so `pool_base + index * 4096` and `pool_base + (index << 12)`
// are one form (the OS pilot's page_pa, which exceeded the bit-level
// budget as a 64-bit sum of two unknowns). A mask that does not cover the
// operand keeps the form nonlinear.
func TestLinearFormSeesThroughLowMasks(t *testing.T) {
	index := &term{kind: termParam, width: 64, name: "index", declared: 16}
	base := paramTerm("pool_base", 64)
	oak := binaryTerm("add", base, binaryTerm("mul", binaryTerm("and", index, constTerm(0xFFFF, 64)), constTerm(4096, 64)))
	machine := binaryTerm("add", base, binaryTerm("shl", zeroExtend(binaryTerm("and", truncate(index, 32), constTerm(65535, 32)), 64), constTerm(12, 64)))
	l, r := oak.linearAt(64), machine.linearAt(64)
	if l == nil || r == nil {
		t.Fatalf("both forms must be linear: oak %v, machine %v", l, r)
	}
	if !l.equal(r) {
		t.Fatalf("the forms differ: oak %s, machine %s", l, r)
	}
	if c := l.coeffs["index"]; c != 4096 || l.coeffs["pool_base"] != 1 {
		t.Fatalf("unexpected coefficients: %s", l)
	}
	// The machine's read of the argument register: the unspecified upper
	// bits beside the u16 value, cleared by the mask.
	hi := paramTerm("index#hi", 32)
	read := binaryTerm("and", binaryTerm("or", binaryTerm("shl", hi, constTerm(16, 32)), truncate(index, 32)), constTerm(65535, 32))
	viaRegister := binaryTerm("add", base, binaryTerm("shl", zeroExtend(read, 64), constTerm(12, 64)))
	if v := viaRegister.linearAt(64); v == nil || !v.equal(l) {
		t.Fatalf("the register read must strip its upper bits: %v vs %s", v, l)
	}
	// A mask narrower than the parameter is not the identity.
	narrow := binaryTerm("and", index, constTerm(0xFF, 64))
	if narrow.linearAt(64) != nil {
		t.Fatalf("a mask below the parameter's width must stay nonlinear")
	}
	// A mask that is not low ones is not the identity either.
	holes := binaryTerm("and", index, constTerm(0xFF00, 64))
	if holes.linearAt(64) != nil {
		t.Fatalf("a mask with holes must stay nonlinear")
	}
}
