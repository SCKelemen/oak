package asm

import (
	"strings"
	"testing"
)

// Flags from additions and the single-flag codes (docs/spec/94-assembler.md
// §8): `adds` leaves NZCV as the flags of left + right, so `cs` is the
// carry — unsigned overflow — and the idiomatic saturating add verifies;
// mi/pl/vs/vc read one flag each.
func TestVerifyAddFlags(t *testing.T) {
	satDecl := "sat_add: (a, b: u32) -> u32"
	satBody := "a + b < a ? u32(0xFFFFFFFF) | a + b"
	idiom := verifyCase(t, satDecl, satBody, "  bind w0 = a\n  bind w1 = b\n  clobber w9, w10\n  adds w9, w0, w1\n  mov w10, #-1\n  csel w0, w10, w9, cs\n  ret")
	if idiom.Kind != VerdictProven {
		t.Fatalf("adds/csel cs saturating add must be proven, got %s: %s", idiom.Kind, idiom.Message)
	}
	// The carry as a Bool result: cset cs is `a + b < a`.
	carry := verifyCase(t, "carries: (a, b: u32) -> Bool", "a + b < a", "  bind w0 = a\n  bind w1 = b\n  clobber w9\n  adds w9, w0, w1\n  cset w0, cs\n  ret")
	if carry.Kind != VerdictProven {
		t.Fatalf("cset cs after adds must be the unsigned overflow, got %s: %s", carry.Kind, carry.Message)
	}
	// Reading the carry with the subtraction sense (`lo`) is a mismatch.
	wrong := verifyCase(t, satDecl, satBody, "  bind w0 = a\n  bind w1 = b\n  clobber w9, w10\n  adds w9, w0, w1\n  mov w10, #-1\n  csel w0, w10, w9, lo\n  ret")
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("csel lo after adds must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
	// 64-bit carry through x registers.
	wide := verifyCase(t, "sat64: (a, b: u64) -> u64", "a + b < a ? u64(0xFFFFFFFFFFFFFFFF) | a + b", "  bind x0 = a\n  bind x1 = b\n  clobber x9, x10\n  adds x9, x0, x1\n  mov x10, #-1\n  csel x0, x10, x9, cs\n  ret")
	if wide.Kind != VerdictProven {
		t.Fatalf("64-bit saturating add must be proven, got %s: %s", wide.Kind, wide.Message)
	}
	// mi after cmp is the difference's sign bit; vs after adds is signed
	// overflow of the sum, spelled in Oak as the sign-bit test.
	negative := verifyCase(t, "below: (a, b: u32) -> Bool", "((a - b) >> u32(31)) == u32(1)", "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  cset w0, mi\n  ret")
	if negative.Kind != VerdictProven {
		t.Fatalf("mi must be the sign bit of a - b, got %s: %s", negative.Kind, negative.Message)
	}
	overflow := verifyCase(t, "sovf: (a, b: u32) -> Bool", "(((a ^ (a + b)) & (b ^ (a + b))) >> u32(31)) == u32(1)", "  bind w0 = a\n  bind w1 = b\n  clobber w9\n  adds w9, w0, w1\n  cset w0, vs\n  ret")
	if overflow.Kind != VerdictProven {
		t.Fatalf("vs after adds must be signed overflow, got %s: %s", overflow.Kind, overflow.Message)
	}
}

// Compare-and-branch: cbz/cbnz and tbz/tbnz are conditional branches
// without flags; a loop may exit through them.
func TestVerifyCompareAndBranch(t *testing.T) {
	// A count-down accumulate exiting through cbz.
	times := verifyCase(t, "times: (a: u64, n: u32) -> u64",
		"{\n  acc: u64 = u64(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + a\n    i = i + u32(1)\n  }\n  acc\n}",
		"  bind x0 = a\n  bind w1 = n\n  clobber x10\n  mov x10, #0\nloop:\n  cbz w1, done\n  add x10, x10, x0\n  sub w1, w1, #1\n  b loop\ndone:\n  mov x0, x10\n  ret")
	if times.Kind != VerdictProven || !strings.Contains(times.Message, "r1 = ") {
		t.Fatalf("a cbz count-down must be proven by the affine coupling, got %s: %s", times.Kind, times.Message)
	}
	// A bit test: odd numbers via tbz on bit 0.
	odd := verifyCase(t, "is_odd: (v: u32) -> Bool", "(v & u32(1)) != u32(0)", "  bind w0 = v\n  tbz w0, #0, even\n  mov w0, #1\n  ret\neven:\n  mov w0, #0\n  ret")
	if odd.Kind != VerdictProven {
		t.Fatalf("tbz bit test must be proven, got %s: %s", odd.Kind, odd.Message)
	}
	// tbnz on the sign bit of a 64-bit value.
	sign := verifyCase(t, "negative: (v: u64) -> Bool", "(v >> u64(63)) == u64(1)", "  bind x0 = v\n  tbnz x0, #63, yes\n  mov x0, #0\n  ret\nyes:\n  mov x0, #1\n  ret")
	if sign.Kind != VerdictProven {
		t.Fatalf("tbnz sign test must be proven, got %s: %s", sign.Kind, sign.Message)
	}
	// The wrong bit is a mismatch.
	wrongBit := verifyCase(t, "is_odd: (v: u32) -> Bool", "(v & u32(1)) != u32(0)", "  bind w0 = v\n  tbz w0, #1, even\n  mov w0, #1\n  ret\neven:\n  mov w0, #0\n  ret")
	if wrongBit.Kind != VerdictMismatch {
		t.Fatalf("testing the wrong bit must be a mismatch, got %s: %s", wrongBit.Kind, wrongBit.Message)
	}
	// The checker: a bit index past the register width is refused; a cbz
	// of an unbound register is an uninitialized read.
	if findings := checkBody(t, "f: (v: u32) -> u32", "  bind w0 = v\n  tbz w0, #32, out\n  ret\nout:\n  mov w0, #0\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "outside") {
		t.Fatalf("a bit past the width must be refused, got %v", findings)
	}
	if findings := checkBody(t, "f: (v: u32) -> u32", "  bind w0 = v\n  clobber w9\n  cbz w9, out\n  ret\nout:\n  mov w0, #0\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "uninitialized") {
		t.Fatalf("cbz of an unwritten register must be refused, got %v", findings)
	}
}
