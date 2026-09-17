package asm

import "testing"

// Two spellings of one packed pair of 32-bit words — the machine's
// `h0 or (h1 shl 32)` and the Oak pack's `(h0 and 0xffffffff) or ((h1 and
// 0xffffffff) shl 32)` — are one header value to the coupling
// (docs/spec/94-assembler.md §9 "Loop invariants"); a pair with the words
// swapped is not.
func TestHeadersEqualAcrossSpellings(t *testing.T) {
	widthOf := func(string) int { return 32 }
	h0, h1 := paramTerm("state.h[0]", 32), paramTerm("state.h[1]", 32)
	machine := binaryTerm("or", zeroExtend(h0, 64), binaryTerm("shl", zeroExtend(h1, 64), constTerm(32, 64)))
	mask := constTerm(0xffffffff, 64)
	oak := binaryTerm("or", binaryTerm("and", zeroExtend(h0, 64), mask), binaryTerm("shl", binaryTerm("and", zeroExtend(h1, 64), mask), constTerm(32, 64)))
	if !headersEqual(machine, oak, widthOf) {
		t.Fatalf("the two spellings of the packed pair must be one header value:\n  %s\n  %s", machine, oak)
	}
	swapped := binaryTerm("or", zeroExtend(h1, 64), binaryTerm("shl", zeroExtend(h0, 64), constTerm(32, 64)))
	if headersEqual(machine, swapped, widthOf) {
		t.Fatal("the pair with its words swapped is a different value")
	}
}
