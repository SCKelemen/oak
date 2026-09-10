package asm

import (
	"strings"
	"testing"
)

// Bit-field instructions, conditional compare, conditional increment and
// negate, and multiply-add (docs/spec/94-assembler.md §7–§8).
func TestVerifyFieldsAndConditionals(t *testing.T) {
	// ubfx is the shift-and-mask extractor spelled directly.
	extract := verifyCase(t, "field: (v: u32) -> u32", "(v >> u32(3)) & u32(3)", "  bind w0 = v\n  ubfx w0, w0, #3, #2\n  ret")
	if extract.Kind != VerdictProven {
		t.Fatalf("ubfx must be proven, got %s: %s", extract.Kind, extract.Message)
	}
	wrongWidth := verifyCase(t, "field: (v: u32) -> u32", "(v >> u32(3)) & u32(3)", "  bind w0 = v\n  ubfx w0, w0, #3, #3\n  ret")
	if wrongWidth.Kind != VerdictMismatch {
		t.Fatalf("a wider field must be a mismatch, got %s: %s", wrongWidth.Kind, wrongWidth.Message)
	}
	// ubfiz places a masked field; bfi inserts it into an existing value.
	place := verifyCase(t, "place: (v: u32) -> u32", "(v & u32(0xF)) << u32(8)", "  bind w0 = v\n  ubfiz w0, w0, #8, #4\n  ret")
	if place.Kind != VerdictProven {
		t.Fatalf("ubfiz must be proven, got %s: %s", place.Kind, place.Message)
	}
	insert := verifyCase(t, "insert: (d, s: u32) -> u32", "(d & ^u32(0xF0)) | ((s & u32(0xF)) << u32(4))", "  bind w0 = d\n  bind w1 = s\n  bfi w0, w1, #4, #4\n  ret")
	if insert.Kind != VerdictProven {
		t.Fatalf("bfi must be proven, got %s: %s", insert.Kind, insert.Message)
	}
	// sbfx sign-extends the field: the Oak spelling shifts it to the top
	// and back down through the bit pattern (no signed shift in Oak, so
	// through u32 arithmetic: the field's sign bit replicated by
	// subtraction).
	signExtend := verifyCase(t, "sfield: (v: u32) -> u32", "((v >> u32(4)) & u32(0xFF)) ^ (((v >> u32(11)) & u32(1)) * u32(0xFFFFFF00))",
		"  bind w0 = v\n  sbfx w0, w0, #4, #8\n  ret")
	if signExtend.Kind != VerdictProven {
		t.Fatalf("sbfx must be proven, got %s: %s", signExtend.Kind, signExtend.Message)
	}
	// The checker bounds the field.
	if findings := checkBody(t, "f: (v: u32) -> u32", "  bind w0 = v\n  ubfx w0, w0, #30, #4\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "not inside") {
		t.Fatalf("a field past the register must be refused, got %v", findings)
	}
	// ccmp: the range check `lo <= v && v < hi` as one flag chain; the
	// immediate nzcv for the failing first test must clear `lo` (C set).
	rangeDecl := "in_range: (v, lo, hi: u32) -> Bool"
	rangeBody := "lo <= v && v < hi"
	chain := verifyCase(t, rangeDecl, rangeBody, "  bind w0 = v\n  bind w1 = lo\n  bind w2 = hi\n  cmp w0, w1\n  ccmp w0, w2, #2, hs\n  cset w0, lo\n  ret")
	if chain.Kind != VerdictProven {
		t.Fatalf("the ccmp range chain must be proven, got %s: %s", chain.Kind, chain.Message)
	}
	wrongImm := verifyCase(t, rangeDecl, rangeBody, "  bind w0 = v\n  bind w1 = lo\n  bind w2 = hi\n  cmp w0, w1\n  ccmp w0, w2, #0, hs\n  cset w0, lo\n  ret")
	if wrongImm.Kind != VerdictMismatch {
		t.Fatalf("nzcv #0 leaves lo true on the failing path: must be a mismatch, got %s: %s", wrongImm.Kind, wrongImm.Message)
	}
	// cinc and cneg.
	inc := verifyCase(t, "bump: (a, b: u32) -> u32", "a < b ? a + u32(1) | a", "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  cinc w0, w0, lo\n  ret")
	if inc.Kind != VerdictProven {
		t.Fatalf("cinc must be proven, got %s: %s", inc.Kind, inc.Message)
	}
	negate := verifyCase(t, "abs_diff: (a, b: u32) -> u32", "a < b ? u32(0) - (a - b) | a - b", "  bind w0 = a\n  bind w1 = b\n  clobber w9\n  sub w9, w0, w1\n  cmp w0, w1\n  cneg w0, w9, lo\n  ret")
	if negate.Kind != VerdictProven {
		t.Fatalf("cneg must be proven, got %s: %s", negate.Kind, negate.Message)
	}
	// madd by a constant stays linear; msub too.
	fma := verifyCase(t, "fma3: (a, c: u32) -> u32", "a * u32(3) + c", "  bind w0 = a\n  bind w1 = c\n  clobber w9\n  mov w9, #3\n  madd w0, w0, w9, w1\n  ret")
	if fma.Kind != VerdictProven || !strings.Contains(fma.Message, "3*a") {
		t.Fatalf("madd by a constant must be proven linearly, got %s: %s", fma.Kind, fma.Message)
	}
	fms := verifyCase(t, "fms3: (a, c: u32) -> u32", "c - a * u32(3)", "  bind w0 = a\n  bind w1 = c\n  clobber w9\n  mov w9, #3\n  msub w0, w0, w9, w1\n  ret")
	if fms.Kind != VerdictProven {
		t.Fatalf("msub by a constant must be proven, got %s: %s", fms.Kind, fms.Message)
	}
}
