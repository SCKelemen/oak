package asm

import (
	"strings"
	"testing"
)

// The machine's trap paths leave the input domain (pathEffects.trap): a
// body that traps under a condition Oak also traps under is compared on
// the other inputs only. Here the asm traps on b = 0 and otherwise returns
// a, while the Oak body gives 7 at b = 0 — a difference on inputs where the
// machine trapped, so no mismatch; the same body without the trap is one.
func TestVerifyTrapDomain(t *testing.T) {
	guarded := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a",
		"  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  ret\ntrap:\n  brk #1")
	if guarded.Kind != VerdictProven {
		t.Errorf("a difference only where the machine traps must not be a mismatch, got %s: %s", guarded.Kind, guarded.Message)
	}
	unguarded := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a",
		"  bind w0 = a\n  bind w1 = b\n  ret")
	if unguarded.Kind != VerdictMismatch {
		t.Errorf("without the trap the difference at b = 0 is a mismatch, got %s: %s", unguarded.Kind, unguarded.Message)
	}
	// A trap on one arm of a nested fork excludes exactly that arm's inputs.
	nested := verifyCase(t, "pick2: (a, b: u32) -> u32", "a < u32(10) ? (b == u32(0) ? u32(7) | a) | b",
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  mov w0, w1\n  ret\ntrap:\n  brk #1")
	if nested.Kind != VerdictProven {
		t.Errorf("a nested trap arm must leave only its inputs, got %s: %s", nested.Kind, nested.Message)
	}
	// The guard's inputs stay in the domain on the other arm: b = 0 with
	// a >= 10 returns b on both sides; returning a there is a mismatch.
	wrongArm := verifyCase(t, "pick2: (a, b: u32) -> u32", "a < u32(10) ? (b == u32(0) ? u32(7) | a) | b",
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  ret\ntrap:\n  brk #1")
	if wrongArm.Kind != VerdictMismatch {
		t.Errorf("the other arm's inputs stay in the domain, got %s: %s", wrongArm.Kind, wrongArm.Message)
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
