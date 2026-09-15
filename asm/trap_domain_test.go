package asm

import (
	"strings"
	"testing"
)

// The machine's trap paths leave the input domain (pathEffects.trap) on
// the claim that Oak traps there too, and witness inputs check the claim
// (machineTrapsWhereOakYields): an asm that traps on b = 0 against an Oak
// body returning 7 there is a mismatch — the machine traps where Oak
// yields a value — while against an Oak body asserting b != 0 it is
// proven, the two differing only where both trap; the same asm without
// the trap is a mismatch against either.
func TestVerifyTrapDomain(t *testing.T) {
	trapping := "  bind w0 = a\n  bind w1 = b\n  cbz w1, trap\n  ret\ntrap:\n  brk #1"
	yields := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a", trapping)
	if yields.Kind != VerdictMismatch || !strings.Contains(yields.Message, "traps where Oak yields") {
		t.Errorf("the machine trapping where the Oak body yields a value must be a mismatch, got %s: %s", yields.Kind, yields.Message)
	}
	asserting := "{\n  assert(b != u32(0))\n  a\n}"
	agreeing := verifyCase(t, "pick: (a, b: u32) -> u32", asserting, trapping)
	if agreeing.Kind != VerdictProven {
		t.Errorf("a difference only where both sides trap must not be a mismatch, got %s: %s", agreeing.Kind, agreeing.Message)
	}
	unguarded := verifyCase(t, "pick: (a, b: u32) -> u32", "b == u32(0) ? u32(7) | a",
		"  bind w0 = a\n  bind w1 = b\n  ret")
	if unguarded.Kind != VerdictMismatch {
		t.Errorf("without the trap the difference at b = 0 is a mismatch, got %s: %s", unguarded.Kind, unguarded.Message)
	}
	// A trap on one arm of a nested fork excludes exactly that arm's
	// inputs, where the Oak arm asserts the same.
	nestedOak := "a < u32(10) ? {\n  assert(b != u32(0))\n  a\n} | {\n  b\n}"
	nested := verifyCase(t, "pick2: (a, b: u32) -> u32", nestedOak,
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  mov w0, w1\n  ret\ntrap:\n  brk #1")
	if nested.Kind != VerdictProven {
		t.Errorf("a nested trap arm must leave only its inputs, got %s: %s", nested.Kind, nested.Message)
	}
	// The guard's inputs stay in the domain on the other arm: b = 0 with
	// a >= 10 returns b on both sides; returning a there is a mismatch.
	wrongArm := verifyCase(t, "pick2: (a, b: u32) -> u32", nestedOak,
		"  bind w0 = a\n  bind w1 = b\n  cmp w0, #10\n  b.hs other\n  cbz w1, trap\n  ret\nother:\n  ret\ntrap:\n  brk #1")
	if wrongArm.Kind != VerdictMismatch {
		t.Errorf("the other arm's inputs stay in the domain, got %s: %s", wrongArm.Kind, wrongArm.Message)
	}
	// An arm speculated by the backend whose guard traps on the inputs
	// of the other arm (a shift count from the other arm's arithmetic):
	// the machine traps where the Oak body, taking the other arm, yields.
	speculated := verifyCase(t, "place: (b: u32, k: u32) -> u32", "k < u32(8) ? b << (k * u32(4)) | b >> ((k - u32(8)) * u32(4))",
		"  bind w0 = b\n  bind w1 = k\n  clobber x9, x10, x11\n  lsl w9, w1, #2\n  cmp w9, #32\n  b.hs trap\n  lsl w10, w0, w9\n  sub w9, w1, #8\n  lsl w9, w9, #2\n  cmp w9, #32\n  b.hs trap\n  lsr w11, w0, w9\n  cmp w1, #8\n  csel w0, w10, w11, lo\n  ret\ntrap:\n  brk #1")
	if speculated.Kind != VerdictMismatch || !strings.Contains(speculated.Message, "traps where Oak yields") {
		t.Errorf("a speculated arm whose guard traps must be a mismatch, got %s: %s", speculated.Kind, speculated.Message)
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
