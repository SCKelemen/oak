package asm

import (
	"strings"
	"testing"
)

// A load from an owned frame array at a data-dependent index (docs/spec/
// 94-assembler.md §8, frame loads at a data-dependent index): under the
// checker's guard `cmp wI, #K; b.hs trap` the load reads the K elements
// merged under the index, the same fold as the Oak side's, so the body is
// proven; a body reading a different element order is refuted; without
// the guard the checker refuses the load.
func TestVerifyFrameLoadAtIndex(t *testing.T) {
	// signed_bytes: (i: u32) -> i32 { bytes: [3]i8 = [i8(-1), i8(2), i8(-3)]; i32(bytes[i]) }
	asmBody := "  bind w0 = i\n  clobber x9, x10\n  frame 32\n  sub sp, sp, #32\n  movz w9, #255\n  strb w9, [sp, #16]\n  movz w9, #2\n  strb w9, [sp, #17]\n  movz w9, #253\n  strb w9, [sp, #18]\n  add x10, sp, #16\n  cmp w0, #3\n  b.hs trap\n  ldrsb w0, [x10, w0, uxtw]\n  add sp, sp, #32\n  ret\ntrap:\n  brk #1"
	oak := "{\n  bytes: [3]i8 = [i8(-1), i8(2), i8(-3)]\n  i32(bytes[i])\n}"
	if v := verifyCase(t, "signed_bytes: (i: u32) -> i32", oak, asmBody); v.Kind != VerdictProven {
		t.Fatalf("a guarded frame load at a data-dependent index must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "signed_bytes: (i: u32) -> i32", "{\n  bytes: [3]i8 = [i8(-1), i8(-3), i8(2)]\n  i32(bytes[i])\n}", asmBody); v.Kind != VerdictMismatch {
		t.Fatalf("a different element order must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// The checker admits the indexed frame load only under the guard, so
	// an unguarded one never reaches the verifier.
	unguarded := strings.Replace(asmBody, "  cmp w0, #3\n  b.hs trap\n", "", 1)
	unit, errs := ParseUnit("v.oakasm", "signed_bytes: (i: u32) -> i32 = {\n"+unguarded+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature("signed_bytes: (i: u32) -> i32")
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) == 0 {
		t.Fatalf("an unguarded frame load at a data-dependent index must be refused by the checker")
	}
}
