package asm

import (
	"strings"
	"testing"
)

// Division and remainder by a variable (docs/spec/20-types.md section
// 11.1): Oak traps on a zero divisor and is total otherwise. The asm
// verifier meets the machine's own guard — the trap path leaves the input
// domain (pathEffects.trap) — and decides the division by witnesses (the
// bit-level decision does not reach it). A body that divides without the
// guard disagrees at zero, where Oak traps and the machine yields zero.
func TestVerifyDivision(t *testing.T) {
	guardedU := "  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  udiv w0, w0, w1\n  ret\ntrap:\n  brk #1"
	v := verifyCase(t, "quot: (a, b: u32) -> u32", "a / b", guardedU)
	if v.Kind != VerdictProven && v.Kind != VerdictWitnessed {
		t.Errorf("a guarded udiv must be proven or witnessed against a / b, got %s: %s", v.Kind, v.Message)
	}
	rem := verifyCase(t, "residue: (a, b: u32) -> u32", "a % b", "  bind w0 = a\n  bind w1 = b\n  clobber x8\n  cbz w1, trap\n  udiv w8, w0, w1\n  msub w0, w8, w1, w0\n  ret\ntrap:\n  brk #1")
	if rem.Kind != VerdictProven && rem.Kind != VerdictWitnessed {
		t.Errorf("a guarded udiv/msub must be proven or witnessed against a %% b, got %s: %s", rem.Kind, rem.Message)
	}
	// Signed: MIN / -1 wraps to MIN on both sides (sdiv's own totalization).
	signed := verifyCase(t, "squot: (a, b: i32) -> i32", "a / b", "  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  sdiv w0, w0, w1\n  ret\ntrap:\n  brk #1")
	if signed.Kind != VerdictProven && signed.Kind != VerdictWitnessed {
		t.Errorf("a guarded sdiv must be proven or witnessed against a / b, got %s: %s", signed.Kind, signed.Message)
	}
	// Without the guard the machine yields zero where Oak traps: a mismatch.
	unguarded := verifyCase(t, "quot: (a, b: u32) -> u32", "a / b", "  bind w0 = a\n  bind w1 = b\n  udiv w0, w0, w1\n  ret")
	if unguarded.Kind != VerdictMismatch {
		t.Errorf("an unguarded udiv must be a mismatch against a / b, got %s: %s", unguarded.Kind, unguarded.Message)
	}
	// The wrong operation under the guard is a mismatch too.
	wrong := verifyCase(t, "quot: (a, b: u32) -> u32", "a / b", "  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  mul w0, w0, w1\n  ret\ntrap:\n  brk #1")
	if wrong.Kind != VerdictMismatch {
		t.Errorf("a multiply under the guard must be a mismatch against a / b, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// ldapr, the RCpc acquire load the Apple cores' compilers emit, reads the
// element as ldar does.
func TestVerifyAcquireLoadRCpc(t *testing.T) {
	v := verifyCase(t, "peek: (v: [*]Atomic[u32], i: u32) -> u32", "atomic_load_acquire(v[i])",
		"  bind x0, w1 = v\n  bind w2 = i\n  clobber x8\n  cmp w2, w1\n  b.hs trap\n  add x8, x0, w2, uxtw #2\n  ldapr w0, [x8]\n  ret\ntrap:\n  brk #1")
	if v.Kind != VerdictProven {
		t.Errorf("an ldapr of a cell must be proven against the atomic load, got %s: %s", v.Kind, v.Message)
	}
	if !strings.Contains(v.Message, "peek") {
		t.Errorf("the verdict names the unit: %s", v.Message)
	}
}
