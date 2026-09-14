package asm

import (
	"strings"
	"testing"
)

// A unit body without effects (docs/spec/94-assembler.md §8, unit bodies
// without effects): neither side writes a package cell or a span memory,
// so the entry state is the final state on both and the body is proven;
// a body that does store through a span the signature lacks stays trusted
// as before.
func TestVerifyUnitBodyWithoutEffects(t *testing.T) {
	v := verifyCase(t, "check: (a: u32) -> ()", "{\n  assert(a == a)\n}", "  bind w0 = a\n  ret")
	if v.Kind != VerdictProven || !strings.Contains(v.Message, "no package state and no span memory") {
		t.Fatalf("a unit body without effects must be proven, got %s: %s", v.Kind, v.Message)
	}
	v = verifyCase(t, "check: (a: u32) -> ()", "{\n  assert(a == a)\n}", "  bind w0 = a\n  clobber x9\n  movz w9, #3\n  ret")
	if v.Kind != VerdictProven {
		t.Fatalf("a unit body writing only scratch registers must be proven, got %s: %s", v.Kind, v.Message)
	}
}
