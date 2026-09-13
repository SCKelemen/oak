package asm

import (
	"strings"
	"testing"
)

// Memory effects through span parameters are verified, not trusted
// (docs/spec/94-assembler.md §9, the twenty-eighth increment): a store
// through a span is compared element by element with the Oak body's, a
// read after a write sees the write on both sides, a conditional store
// meets the entry memory on the other arm, and a wrong store is a
// mismatch naming the span.
func TestVerifySpanWriters(t *testing.T) {
	// set: (v: [*]u32, i: u32, x: u32) -> () { v[i] = x }: a unit writer.
	set := verifyCase(t, "set: (v: [*]u32, i: u32, x: u32) -> ()", "{\n  v[i] = x\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  cmp w2, w1\n  b.hs trap\n  str w3, [x0, w2, uxtw #2]\n  ret\ntrap:\n  brk #1")
	if set.Kind != VerdictProven || !strings.Contains(set.Message, "the span memory it writes (v)") {
		t.Fatalf("a unit writer must be proven in its span, got %s: %s", set.Kind, set.Message)
	}
	// The wrong lowering: stores x + 1 where the body stores x.
	wrong := verifyCase(t, "set_x: (v: [*]u32, i: u32, x: u32) -> ()", "{\n  v[i] = x\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add w9, w3, #1\n  str w9, [x0, w2, uxtw #2]\n  ret\ntrap:\n  brk #1")
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "the span v") {
		t.Fatalf("a wrong store must be a mismatch naming the span, got %s: %s", wrong.Kind, wrong.Message)
	}
	// A store at the wrong element is a mismatch too.
	misplaced := verifyCase(t, "set_at: (v: [*]u32, i: u32, x: u32) -> ()", "{\n  v[i] = x\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  cmp w1, #1\n  b.lo trap\n  str w3, [x0]\n  ret\ntrap:\n  brk #1")
	if misplaced.Kind != VerdictMismatch {
		t.Fatalf("a store at another element must be a mismatch, got %s: %s", misplaced.Kind, misplaced.Message)
	}
	// guarded: a store on one arm meets the entry memory on the other.
	guarded := verifyCase(t, "guarded: (v: [*]u32, i: u32, x: u32) -> ()", "{\n  x > u32(10) ? { v[i] = x } | { }\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  cmp w3, #10\n  b.ls done\n  cmp w2, w1\n  b.hs trap\n  str w3, [x0, w2, uxtw #2]\ndone:\n  ret\ntrap:\n  brk #1")
	if guarded.Kind != VerdictProven {
		t.Fatalf("a conditional writer must be proven, got %s: %s", guarded.Kind, guarded.Message)
	}
	// A conditional store the asm makes unconditionally is a mismatch.
	unguarded := verifyCase(t, "unguarded: (v: [*]u32, i: u32, x: u32) -> ()", "{\n  x > u32(10) ? { v[i] = x } | { }\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = x\n  cmp w2, w1\n  b.hs trap\n  str w3, [x0, w2, uxtw #2]\n  ret\ntrap:\n  brk #1")
	if unguarded.Kind != VerdictMismatch {
		t.Fatalf("an unconditional store for a conditional body must be a mismatch, got %s: %s", unguarded.Kind, unguarded.Message)
	}
	// bump: a result and a write: the read after the write is the written
	// value on both sides, though the asm forwards it from the register.
	bump := verifyCase(t, "bump: (v: [*]u32, x: u32) -> u32", "{\n  v[0] = x + u32(1)\n  v[0] * u32(2)\n}",
		"  bind x0, w1 = v\n  bind w2 = x\n  clobber x9\n  cmp w1, #1\n  b.lo trap\n  add w9, w2, #1\n  str w9, [x0]\n  lsl w0, w9, #1\n  ret\ntrap:\n  brk #1")
	if bump.Kind != VerdictProven || !strings.Contains(bump.Message, "and the span memory it writes (v)") {
		t.Fatalf("a writer with a result must be proven in both, got %s: %s", bump.Kind, bump.Message)
	}
	// swap: two elements read, then written crosswise; the asm reads both
	// before storing, as the body's order requires.
	swap := verifyCase(t, "swap: (v: [*]u8, i: u32, j: u32) -> ()", "{\n  a: u8 = v[i]\n  b: u8 = v[j]\n  v[i] = b\n  v[j] = a\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = j\n  clobber x9, x10\n  cmp w2, w1\n  b.hs trap\n  ldrb w9, [x0, w2, uxtw]\n  cmp w3, w1\n  b.hs trap\n  ldrb w10, [x0, w3, uxtw]\n  strb w10, [x0, w2, uxtw]\n  strb w9, [x0, w3, uxtw]\n  ret\ntrap:\n  brk #1")
	if swap.Kind != VerdictProven {
		t.Fatalf("a swap must be proven, got %s: %s", swap.Kind, swap.Message)
	}
	// A swap that stores in the wrong order (the second store reads the
	// first's value) is refuted: when i == j the memories differ.
	stale := verifyCase(t, "swap_stale: (v: [*]u8, i: u32, j: u32) -> ()", "{\n  a: u8 = v[i]\n  b: u8 = v[j]\n  v[i] = b\n  v[j] = a\n}",
		"  bind x0, w1 = v\n  bind w2 = i\n  bind w3 = j\n  clobber x9, x10\n  cmp w2, w1\n  b.hs trap\n  ldrb w9, [x0, w2, uxtw]\n  cmp w3, w1\n  b.hs trap\n  strb w9, [x0, w3, uxtw]\n  ldrb w10, [x0, w3, uxtw]\n  strb w10, [x0, w2, uxtw]\n  ret\ntrap:\n  brk #1")
	if stale.Kind != VerdictMismatch {
		t.Fatalf("a reordered swap must be a mismatch, got %s: %s", stale.Kind, stale.Message)
	}
	// A store the Oak body does not make is a mismatch.
	extra := verifyCase(t, "peek: (v: [*]u32, x: u32) -> u32", "{\n  v[0] + x\n}",
		"  bind x0, w1 = v\n  bind w2 = x\n  clobber x9\n  cmp w1, #1\n  b.lo trap\n  ldr w9, [x0]\n  str w2, [x0]\n  add w0, w9, w2\n  ret\ntrap:\n  brk #1")
	if extra.Kind != VerdictMismatch || !strings.Contains(extra.Message, "the span v") {
		t.Fatalf("a store the body does not make must be a mismatch, got %s: %s", extra.Kind, extra.Message)
	}
}
