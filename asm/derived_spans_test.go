package asm

import "testing"

// spanAddressOf flattens a derived span's base (docs/spec/94-assembler.md
// §8, derived spans): the root's base plus scaled index terms and whole-
// element constants, nested as a re-slice nests them; a constant that is
// not whole elements, a scale that is not the element size, or two bases
// are refused.
func TestSpanAddressOf(t *testing.T) {
	base := paramTerm(spanBaseName("v"), 64)
	start := paramTerm("start", 32)
	i := paramTerm("i", 32)
	scaled := func(x *term) *term { return binaryTerm("shl", zeroExtend(x, 64), constTerm(1, 64)) }
	nested := binaryTerm("add", binaryTerm("add", base, scaled(start)), scaled(i))
	root, index, ok := spanAddressOf(nested, 2)
	if !ok || root != "v" || index == nil {
		t.Fatalf("a re-sliced base must resolve to the root: %v %v %v", root, index, ok)
	}
	if index.kind != termBinary || index.op != "add" || index.width != 32 {
		t.Fatalf("the index must be the 32-bit sum of the starts, got %s", index)
	}
	// A whole-element constant offset is an index too.
	withConst := binaryTerm("add", base, constTerm(4, 64))
	if root, index, ok := spanAddressOf(withConst, 2); !ok || root != "v" || index == nil || index.kind != termConst || index.value != 2 {
		t.Fatalf("a constant offset must count elements: %v %v %v", root, index, ok)
	}
	// Not whole elements: refused.
	if _, _, ok := spanAddressOf(binaryTerm("add", base, constTerm(3, 64)), 2); ok {
		t.Fatalf("a constant that is not whole elements must be refused")
	}
	// The wrong scale: refused (a 4-byte scale over 2-byte elements).
	if _, _, ok := spanAddressOf(binaryTerm("add", base, binaryTerm("shl", zeroExtend(i, 64), constTerm(2, 64))), 2); ok {
		t.Fatalf("a scale that is not the element size must be refused")
	}
	// Two bases: refused.
	if _, _, ok := spanAddressOf(binaryTerm("add", base, paramTerm(spanBaseName("w"), 64)), 1); ok {
		t.Fatalf("two span bases must be refused")
	}
	// The bare base is the span at index nil.
	if root, index, ok := spanAddressOf(base, 4); !ok || root != "v" || index != nil {
		t.Fatalf("the base alone must resolve with no index: %v %v %v", root, index, ok)
	}
}
