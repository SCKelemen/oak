package asm

import "testing"

// Two value identities of the canonicalizer (docs/spec/94-assembler.md §9,
// Oak.BitwiseCanonical): a low-ones mask covering every significant bit of
// its operand is the identity, and the low word of a packed pair is the
// pair masked to the pack's shift. A mask narrower than the operand stays.
func TestCanonicalMaskIdentities(t *testing.T) {
	h := zeroExtend(paramTerm("h", 32), 64)
	if got := canonical(binaryTerm("and", h, constTerm(0xffffffff, 64))); !equalTerms(got, canonical(h)) {
		t.Fatalf("a covering mask must vanish: %s", got)
	}
	if got := canonical(binaryTerm("and", h, constTerm(0xffff, 64))); got.kind != termBinary || got.op != "and" {
		t.Fatalf("a narrower mask must stay: %s", got)
	}
	lo, hi := zeroExtend(paramTerm("lo", 32), 64), zeroExtend(paramTerm("hi", 32), 64)
	pack := binaryTerm("or", lo, binaryTerm("shl", hi, constTerm(32, 64)))
	if got := canonical(binaryTerm("and", pack, constTerm(0xffffffff, 64))); !equalTerms(got, canonical(lo)) {
		t.Fatalf("the low word of a packed pair must be the low operand: %s", got)
	}
	if got := canonical(binaryTerm("shr", pack, constTerm(32, 64))); !equalTerms(got, canonical(hi)) {
		t.Fatalf("the high word of a packed pair must be the high operand: %s", got)
	}
}
