package asm

import (
	"strings"
	"testing"
)

func verifyCase(t *testing.T, decl, oakBody, asmBody string) Verdict {
	t.Helper()
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = " + oakBody)
	if err != nil {
		t.Fatal(err)
	}
	return Verify(unit.Functions[0], sig, spec.Body)
}

// Verdicts are labeled proof / evidence / trusted / mismatch
// (docs/spec/94-assembler.md §8).
func TestVerifyVerdicts(t *testing.T) {
	decl := "add_asm: (left, right: u32) -> u32"
	proven := verifyCase(t, decl, "left + right", "  bind w0 = left\n  bind w1 = right\n  add w0, w0, w1\n  ret")
	if proven.Kind != VerdictProven {
		t.Fatalf("add must be proven, got %s: %s", proven.Kind, proven.Message)
	}
	// Commuted operands and a subtraction spelled as add-of-negation are the
	// same linear form.
	commuted := verifyCase(t, decl, "right + left", "  bind w0 = left\n  bind w1 = right\n  add w0, w1, w0\n  ret")
	if commuted.Kind != VerdictProven {
		t.Fatalf("commuted add must be proven, got %s", commuted.Kind)
	}
	shifted := verifyCase(t, "scale: (a: u64) -> u64", "(a + u64(2)) << 3", "  bind x0 = a\n  clobber x9\n  add x9, x0, #2\n  lsl x0, x9, #3\n  ret")
	if shifted.Kind != VerdictProven {
		t.Fatalf("add-then-shift is linear and must be proven, got %s: %s", shifted.Kind, shifted.Message)
	}

	wrong := verifyCase(t, decl, "left + right", "  bind w0 = left\n  bind w1 = right\n  sub w0, w0, w1\n  ret")
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "disagrees") {
		t.Fatalf("sub for add must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}

	// Beyond the linear form the bit-blaster decides: shift-and-mask,
	// flag composition with or/xor, and a subtraction are proven; a wrong
	// mask is a mismatch with a concrete counterexample.
	masked := verifyCase(t, "low_nibble: (v: u32) -> u32", "(v >> 4) & u32(15)", "  bind w0 = v\n  clobber w9\n  lsr w9, w0, #4\n  and w0, w9, #15\n  ret")
	if masked.Kind != VerdictProven || !strings.Contains(masked.Message, "bit level") {
		t.Fatalf("shift-and-mask must be proven at the bit level, got %s: %s", masked.Kind, masked.Message)
	}
	flags := verifyCase(t, "compose: (a, b: u64) -> u64", "(a | (b << 8)) ^ u64(255)", "  bind x0 = a\n  bind x1 = b\n  clobber x9\n  lsl x9, x1, #8\n  orr x0, x0, x9\n  eor x0, x0, #255\n  ret")
	if flags.Kind != VerdictProven {
		t.Fatalf("or/xor composition must be proven, got %s: %s", flags.Kind, flags.Message)
	}
	wrongMask := verifyCase(t, "low_nibble: (v: u32) -> u32", "(v >> 4) & u32(31)", "  bind w0 = v\n  clobber w9\n  lsr w9, w0, #4\n  and w0, w9, #15\n  ret")
	if wrongMask.Kind != VerdictMismatch || !strings.Contains(wrongMask.Message, "v=") {
		t.Fatalf("a wrong mask must be a mismatch with a counterexample, got %s: %s", wrongMask.Kind, wrongMask.Message)
	}
	// A register shift count: the barrel shifter blasts it and the machine's
	// modulo-width count agrees with Oak only when the Oak side is also a
	// constant shift — so the Oak lowering refuses, and the verdict is
	// trusted rather than a false proof.
	variableShift := verifyCase(t, "shift_by: (v, n: u32) -> u32", "v << n", "  bind w0 = v\n  bind w1 = n\n  lsl w0, w0, w1\n  ret")
	if variableShift.Kind != VerdictTrusted {
		t.Fatalf("a variable shift count must be trusted (Oak traps, the machine wraps), got %s: %s", variableShift.Kind, variableShift.Message)
	}

	memory := verifyCase(t, "spill: (a: u64) -> u64", "a", "  bind x0 = a\n  frame 16\n  str x0, [sp, #-16]!\n  ldr x0, [sp], #16\n  ret")
	if memory.Kind != VerdictTrusted || !strings.Contains(memory.Message, "trusted") {
		t.Fatalf("a memory body must be trusted, got %s: %s", memory.Kind, memory.Message)
	}

	// The 32-bit width law: a w-register add wraps at 32 bits, so the
	// specification 0xFFFFFFFF + 1 == 0 holds and is proven, not mismatched.
	wrap := verifyCase(t, "inc: (a: u32) -> u32", "a + u32(1)", "  bind w0 = a\n  add w0, w0, #1\n  ret")
	if wrap.Kind != VerdictProven {
		t.Fatalf("32-bit wrapping add must be proven, got %s: %s", wrap.Kind, wrap.Message)
	}
}
