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

// The RV64 lane: the element address is formed by the scaled add after
// the guard (`li k, N; bgeu i, k, trap; slli i, i, s; add i, b, i`), the
// guard's bound following the index's term through the rewrite.
func TestRV64VerifyFrameLoadAtIndex(t *testing.T) {
	// signed_bytes: (i: u32) -> i32 { bytes: [3]i8 = [i8(-1), i8(2), i8(-3)]; i32(bytes[i]) }
	asmBody := "  bind a0 = i\n  clobber t0, t1, t2\n  frame 32\n  addi sp, sp, -32\n  li t0, 255\n  sb t0, 16(sp)\n  li t0, 2\n  sb t0, 17(sp)\n  li t0, 253\n  sb t0, 18(sp)\n  slli a0, a0, 32\n  srli a0, a0, 32\n  addi t1, sp, 16\n  li t2, 3\n  bgeu a0, t2, trap\n  add a0, t1, a0\n  lb a0, 0(a0)\n  addi sp, sp, 32\n  ret\ntrap:\n  ebreak"
	oak := "{\n  bytes: [3]i8 = [i8(-1), i8(2), i8(-3)]\n  i32(bytes[i])\n}"
	if v := rv64Verify(t, "signed_bytes: (i: u32) -> i32", oak, asmBody); v.Kind != VerdictProven {
		t.Fatalf("a guarded frame load at a data-dependent index must be proven on rv64, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "signed_bytes: (i: u32) -> i32", "{\n  bytes: [3]i8 = [i8(-1), i8(-3), i8(2)]\n  i32(bytes[i])\n}", asmBody); v.Kind != VerdictMismatch {
		t.Fatalf("a different element order must be a mismatch on rv64, got %s: %s", v.Kind, v.Message)
	}
	// Word elements: the index scaled by the element size.
	words := "  bind a0 = i\n  clobber t0, t1, t2\n  frame 32\n  addi sp, sp, -32\n  li t0, 7\n  sw t0, 16(sp)\n  li t0, 9\n  sw t0, 20(sp)\n  slli a0, a0, 32\n  srli a0, a0, 32\n  addi t1, sp, 16\n  li t2, 2\n  bgeu a0, t2, trap\n  slli a0, a0, 2\n  add a0, t1, a0\n  lw a0, 0(a0)\n  addi sp, sp, 32\n  ret\ntrap:\n  ebreak"
	if v := rv64Verify(t, "pick: (i: u32) -> u32", "{\n  xs: [2]u32 = [u32(7), u32(9)]\n  xs[i]\n}", words); v.Kind != VerdictProven {
		t.Fatalf("a guarded word load at a data-dependent index must be proven on rv64, got %s: %s", v.Kind, v.Message)
	}
}
