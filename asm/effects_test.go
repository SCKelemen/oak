package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
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

// A unit callee's stores reach its caller through the call summary
// (twenty-ninth increment): the callee's span parameter is an alias of
// the caller's span passed whole, so its writes land in the caller's
// memory and a read after the call sees them; a caller that passes a
// subslice, or a callee whose stores the Oak body does not make, stays
// trusted or is refuted.
func TestVerifyCalleeEffects(t *testing.T) {
	putBody := "put: (v: [*]u32, i: u32, x: u32) -> () {\n  v[i] = x\n}"
	put, err := parseSignatureWithBody(putBody)
	if err != nil {
		t.Fatal(err)
	}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = map[string]*ast.FunctionStatement{"put": put}
		if findings := Check(unit.Functions[0], sig, map[string]bool{"put": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	call := "  bind x0, w1 = v\n  bind w2 = k\n  clobber x3, x9, x19, x20, x21, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  stp x19, x20, [sp, #16]\n  str x21, [sp, #32]\n  mov x19, x0\n  mov w20, w1\n  mov w21, w2\n  movz w3, #7\n  bl put\n"
	ret := "  ldp x19, x20, [sp, #16]\n  ldr x21, [sp, #32]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret"
	trapping := ret + "\ntrap:\n  brk #1"
	// put_seven: (v: [*]u32, k: u32) -> () { put(v, k, u32(7)) }: the callee's store is the caller's effect.
	unit := pair(t, "put_seven: (v: [*]u32, k: u32) -> ()", call+ret, "{\n  put(v, k, u32(7))\n}")
	if unit.Kind != VerdictProven || !strings.Contains(unit.Message, "the span memory it writes (v)") {
		t.Fatalf("a unit caller of a unit writer must be proven in its span, got %s: %s", unit.Kind, unit.Message)
	}
	// after_put reads back what the callee stored: the summary's write is
	// visible to the caller's own load.
	after := pair(t, "after_put: (v: [*]u32, k: u32) -> u32", call+"  cmp w21, w20\n  b.hs trap\n  ldr w9, [x19, w21, uxtw #2]\n  add w0, w9, #1\n"+trapping, "{\n  put(v, k, u32(7))\n  v[k] + u32(1)\n}")
	if after.Kind != VerdictProven || !strings.Contains(after.Message, "and the span memory it writes (v)") {
		t.Fatalf("a read after a summarized store must be proven, got %s: %s", after.Kind, after.Message)
	}
	// The Oak body stores 8 where the callee stores 7: refuted in the span.
	wrong := pair(t, "put_eight: (v: [*]u32, k: u32) -> ()", call+ret, "{\n  v[k] = u32(8)\n}")
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "the span v") {
		t.Fatalf("a callee storing another value must be refuted, got %s: %s", wrong.Kind, wrong.Message)
	}
}

// A shift count that cannot reach the width (asm/range.go) is admitted:
// Oak's trapping shift and the machine's wrapping one agree below the
// width; a count whose range reaches it stays outside the subset.
func TestVerifyBoundedShift(t *testing.T) {
	bounded := verifyCase(t, "byte_of: (w: u32, at: u32) -> u32", "(w >> ((at % u32(4)) * u32(8))) & u32(255)",
		"  bind w0 = w\n  bind w1 = at\n  clobber x9\n  and w9, w1, #3\n  lsl w9, w9, #3\n  lsr w0, w0, w9\n  and w0, w0, #255\n  ret")
	if bounded.Kind != VerdictProven {
		t.Fatalf("a shift by a count below the width must be proven, got %s: %s", bounded.Kind, bounded.Message)
	}
	unbounded := verifyCase(t, "shift_by: (w: u32, n: u32) -> u32", "w << n",
		"  bind w0 = w\n  bind w1 = n\n  lsl w0, w0, w1\n  ret")
	if unbounded.Kind != VerdictTrusted || !strings.Contains(unbounded.Message, "non-constant shift count") {
		t.Fatalf("a shift by an unbounded count must stay trusted, got %s: %s", unbounded.Kind, unbounded.Message)
	}
}

// Loop-carried memory (span memories through loops, and the entry
// memories they are inducted from): a fill loop is proven in its memory
// by coupling, a wrong body store is a mismatch on a concrete input, a
// result after the loop is proven with the memory, a store before the
// loop is read after it through the loop's unknown memory — and a store
// before the loop that differs between the sides is never proven, since
// the entry memories are the induction's base.
func TestVerifyLoopStores(t *testing.T) {
	fillOak := "{\n  i: u32 = u32(0)\n  while i < n {\n    v[i] = x\n    i = i + u32(1)\n  }\n}"
	fillAsm := "  bind x0, w1 = v\n  bind w2 = n\n  bind w3 = x\n  clobber w9, w10\n  mov w9, #0\nloop:\n  cmp w9, w2\n  b.hs done\n  cmp w9, w1\n  b.hs trap\n  str w3, [x0, w9, uxtw #2]\n  add w9, w9, #1\n  b loop\ndone:\n  ret\ntrap:\n  brk #1"
	fill := verifyCase(t, "fill: (v: [*]u32, n: u32, x: u32) -> ()", fillOak, fillAsm)
	if fill.Kind != VerdictProven || !strings.Contains(fill.Message, "the span memory it writes (v)") || !strings.Contains(fill.Message, "coupled inductively") {
		t.Fatalf("a fill loop must be proven in its span memory by coupling, got %s: %s", fill.Kind, fill.Message)
	}
	wrong := verifyCase(t, "fill_x: (v: [*]u32, n: u32, x: u32) -> ()", fillOak, strings.Replace(fillAsm, "  str w3, [x0, w9, uxtw #2]", "  add w10, w3, #1\n  str w10, [x0, w9, uxtw #2]", 1))
	if wrong.Kind != VerdictMismatch || !strings.Contains(wrong.Message, "in the span v") {
		t.Fatalf("a wrong loop store must be a mismatch on a concrete input naming the span, got %s: %s", wrong.Kind, wrong.Message)
	}
	counted := verifyCase(t, "fill_count: (v: [*]u32, n: u32, x: u32) -> u32", "{\n  i: u32 = u32(0)\n  while i < n {\n    v[i] = x\n    i = i + u32(1)\n  }\n  i\n}", strings.Replace(fillAsm, "done:\n  ret", "done:\n  mov w0, w9\n  ret", 1))
	if counted.Kind != VerdictProven || !strings.Contains(counted.Message, "the span memory it writes (v)") {
		t.Fatalf("a fill loop with a result must be proven in both, got %s: %s", counted.Kind, counted.Message)
	}
	thenOak := "{\n  v[0] = x\n  i: u32 = u32(1)\n  while i < n {\n    v[i] = x + i\n    i = i + u32(1)\n  }\n  v[0]\n}"
	thenAsm := "  bind x0, w1 = v\n  bind w2 = n\n  bind w3 = x\n  clobber w9, w10\n  cmp w1, #1\n  b.lo trap\n  str w3, [x0]\n  mov w9, #1\nloop:\n  cmp w9, w2\n  b.hs done\n  cmp w9, w1\n  b.hs trap\n  add w10, w3, w9\n  str w10, [x0, w9, uxtw #2]\n  add w9, w9, #1\n  b loop\ndone:\n  ldr w0, [x0]\n  ret\ntrap:\n  brk #1"
	after := verifyCase(t, "fill_then: (v: [*]u32, n: u32, x: u32) -> u32", thenOak, thenAsm)
	if after.Kind != VerdictProven {
		t.Fatalf("a read of the loop's memory after the loop must be proven, got %s: %s", after.Kind, after.Message)
	}
	// The base of the induction: the asm stores x + 1 before the loop
	// where the body stores x. The markers hide the difference from the
	// exit comparison; the entry memories must catch it.
	entry := verifyCase(t, "fill_entry: (v: [*]u32, n: u32, x: u32) -> ()", strings.Replace(thenOak, "\n  v[0]\n}", "\n}", 1), strings.Replace(strings.Replace(thenAsm, "  str w3, [x0]\n", "  add w10, w3, #1\n  str w10, [x0]\n", 1), "done:\n  ldr w0, [x0]\n  ret", "done:\n  ret", 1))
	if entry.Kind == VerdictProven {
		t.Fatalf("a differing store before the loop must never be proven, got %s: %s", entry.Kind, entry.Message)
	}
	if entry.Kind != VerdictMismatch {
		t.Fatalf("a differing store before the loop must be a mismatch on a concrete input, got %s: %s", entry.Kind, entry.Message)
	}
}

// A callee with a data-dependent loop is summarized (docs/spec/94-assembler.md
// §9): the callee's loop events become the caller's, numbered after the
// caller's own, and the Oak side inlining the same body creates the same
// events, which the coupling pairs by identity — a summing callee behind a
// result, a filling unit callee behind a unit caller.
func TestVerifySummarizedLoops(t *testing.T) {
	sum, err := parseSignatureWithBody("sum_loop: (v: []u32, n: u32) -> u32 {\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + v[i]\n    i = i + u32(1)\n  }\n  acc\n}")
	if err != nil {
		t.Fatal(err)
	}
	fill, err := parseSignatureWithBody("fill: (v: [*]u32, n: u32, x: u32) -> () {\n  i: u32 = u32(0)\n  while i < n {\n    v[i] = x\n    i = i + u32(1)\n  }\n}")
	if err != nil {
		t.Fatal(err)
	}
	callees := map[string]*ast.FunctionStatement{"sum_loop": sum, "fill": fill}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = callees
		if findings := Check(unit.Functions[0], sig, map[string]bool{"sum_loop": true, "fill": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	frame := "  clobber x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n"
	leave := "  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret"
	summed := pair(t, "sum_plus: (v: []u32, n: u32) -> u32", "  bind x0, w1 = v\n  bind w2 = n\n"+frame+"  bl sum_loop\n  add w0, w0, #1\n"+leave, "{\n  sum_loop(v, n) + u32(1)\n}")
	if summed.Kind != VerdictProven || !strings.Contains(summed.Message, "coupled inductively") {
		t.Fatalf("a caller of a summing loop must be proven by coupling the callee's loop, got %s: %s", summed.Kind, summed.Message)
	}
	filled := pair(t, "fill_seven: (v: [*]u32, n: u32) -> ()", "  bind x0, w1 = v\n  bind w2 = n\n  clobber x3\n"+strings.Replace(frame, "clobber x29, x30", "clobber x29, x30", 1)+"  movz w3, #7\n  bl fill\n"+leave, "{\n  fill(v, n, u32(7))\n}")
	if filled.Kind != VerdictProven || !strings.Contains(filled.Message, "the span memory it writes (v)") {
		t.Fatalf("a caller of a filling loop must be proven in its span memory, got %s: %s", filled.Kind, filled.Message)
	}
	// The wrong constant: refuted on a concrete input in the span.
	wrong := pair(t, "fill_eight: (v: [*]u32, n: u32) -> ()", "  bind x0, w1 = v\n  bind w2 = n\n  clobber x3\n"+frame+"  movz w3, #8\n  bl fill\n"+leave, "{\n  fill(v, n, u32(7))\n}")
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("a caller passing the wrong value must be a mismatch, got %s: %s", wrong.Kind, wrong.Message)
	}
}
