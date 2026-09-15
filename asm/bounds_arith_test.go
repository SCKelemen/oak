package asm

import (
	"strings"
	"testing"
)

// Bounds through arithmetic (docs/spec/94-assembler.md §7; asm/bounds_arith.go).
// The binary search midpoint: `sub wT, wHi, wLo` under `wLo < wHi`, `lsr
// wT, wT, #1`, `add wMid, wLo, wT` proves `wMid < wHi`
// (Oak.Assembler.midpoint_below); `hi = mid` keeps hi at most the length
// (Oak.Assembler.narrowed_upper), so the element read at the midpoint
// needs no guard of its own.
func TestCheckBinarySearchMidpoint(t *testing.T) {
	decl := "search: (keys: []u64, target: u64) -> u32"
	body := "  bind x0, w1 = keys\n  bind x2 = target\n  clobber x9, x10, x11, x12\n  mov w9, wzr\n  mov w10, w1\nloop:\n  cmp w9, w10\n  b.hs done\n  sub w11, w10, w9\n  lsr w11, w11, #1\n  add w12, w9, w11\n  ldr x11, [x0, w12, uxtw #3]\n  cmp x11, x2\n  b.hs upper\n  add w9, w12, #1\n  b loop\nupper:\n  mov w10, w12\n  b loop\ndone:\n  mov w0, w9\n  ret"
	if findings := checkBody(t, decl, body); len(findings) != 0 {
		t.Fatalf("the midpoint read must be admitted: %v", findings)
	}
	// Without the halving, lo + (hi - lo) = hi: no bound.
	unhalved := strings.Replace(body, "  lsr w11, w11, #1\n", "", 1)
	findings := checkBody(t, decl, unhalved)
	if len(findings) == 0 || !strings.Contains(findings[0], "without a dominating index guard") {
		t.Fatalf("lo + (hi - lo) is not below hi; got %v", findings)
	}
	// A hi that grows on the back edge is no bound at the header: the
	// length registers meet at the label like every other fact.
	growing := strings.Replace(body, "  mov w10, w12\n", "  add w10, w10, #1\n", 1)
	findings = checkBody(t, decl, growing)
	if len(findings) == 0 || !strings.Contains(findings[0], "not this span's length register") {
		t.Fatalf("a bound rewritten upward on the back edge must be refused, got %v", findings)
	}
}

// A length register rewritten on a loop's back edge is not the length at
// the header: the span's length registers join the label meet (the
// fixpoint over the whole register state), so the read below it is refused.
func TestCheckLengthRegisterAcrossBackEdge(t *testing.T) {
	decl := "grow: (a: []u32) -> u32"
	body := "  bind x0, w1 = a\n  clobber x9, x10, x11\n  mov w9, w1\n  mov w10, wzr\nloop:\n  cmp w10, w9\n  b.hs done\n  ldr w11, [x0, w10, uxtw #2]\n  add w9, w9, #1\n  add w10, w10, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	findings := checkBody(t, decl, body)
	if len(findings) == 0 || !strings.Contains(findings[0], "not this span's length register") {
		t.Fatalf("a length copy grown on the back edge must not bound the index, got %v", findings)
	}
	// The same loop with the copy left alone is the counted walk.
	steady := strings.Replace(body, "  add w9, w9, #1\n", "", 1)
	if findings := checkBody(t, decl, steady); len(findings) != 0 {
		t.Fatalf("the counted walk under a length copy must be admitted: %v", findings)
	}
}

// The page probe's outer search: `lsr wP, wL, #9` is at most the length
// shifted (an upper fact), the midpoint is below it, and `lsl wI, wMid, #9`
// under `wMid < wHi <= wL >> 9` proves the slack fact `wI + 512 <= len`
// (Oak.Assembler.shifted_index_slack) — the read at the page's first key
// and at any key inside the page needs no guard.
func TestCheckShiftedIndexUnderQuotient(t *testing.T) {
	decl := "probe: (keys: []u64, target: u64) -> u32"
	body := "  bind x0, w1 = keys\n  bind x2 = target\n  clobber x9, x10, x11, x12, x13\n  lsr w9, w1, #9\n  mov w10, wzr\n  mov w11, w9\nloop:\n  cmp w10, w11\n  b.hs done\n  sub w12, w11, w10\n  lsr w12, w12, #1\n  add w13, w10, w12\n  lsl w12, w13, #9\n  ldr x12, [x0, w12, uxtw #3]\n  cmp x12, x2\n  b.hi upper\n  add w10, w13, #1\n  b loop\nupper:\n  mov w11, w13\n  b loop\ndone:\n  mov w0, w10\n  ret"
	if findings := checkBody(t, decl, body); len(findings) != 0 {
		t.Fatalf("the page's first key must be admitted: %v", findings)
	}
	// Any key inside the page: the slack fact carries through `add #k`, k < 512.
	last := strings.Replace(body, "  ldr x12, [x0, w12, uxtw #3]\n", "  add w12, w12, #511\n  ldr x12, [x0, w12, uxtw #3]\n", 1)
	if findings := checkBody(t, decl, last); len(findings) != 0 {
		t.Fatalf("the page's last key must be admitted: %v", findings)
	}
	past := strings.Replace(body, "  ldr x12, [x0, w12, uxtw #3]\n", "  add w12, w12, #512\n  ldr x12, [x0, w12, uxtw #3]\n", 1)
	findings := checkBody(t, decl, past)
	if len(findings) == 0 {
		t.Fatal("the key past the page must be refused")
	}
	// Scaling by more than the quotient's shift proves nothing.
	wider := strings.Replace(body, "  lsl w12, w13, #9\n", "  lsl w12, w13, #10\n", 1)
	findings = checkBody(t, decl, wider)
	if len(findings) == 0 || !strings.Contains(findings[0], "without a dominating index guard") {
		t.Fatalf("mid << 10 under mid < len >> 9 is unbounded; got %v", findings)
	}
}

// A label's state is the whole register state: a span base advanced on the
// back edge is not the span at the header, and a global's address loaded
// once before a loop still is.
func TestCheckRegisterStateAtLabels(t *testing.T) {
	decl := "walk: (a: []u32) -> u32"
	moving := "  bind x0, w1 = a\n  clobber x9, x10, x11\n  mov x9, x0\n  mov w10, wzr\nloop:\n  cmp w10, w1\n  b.hs done\n  ldr w11, [x9, w10, uxtw #2]\n  add x9, x9, #4\n  add w10, w10, #1\n  b loop\ndone:\n  mov w0, w10\n  ret"
	findings := checkBody(t, decl, moving)
	if len(findings) == 0 {
		t.Fatal("a base advanced on the back edge is not the span at the header")
	}
	steady := strings.Replace(moving, "  add x9, x9, #4\n", "", 1)
	if findings := checkBody(t, decl, steady); len(findings) != 0 {
		t.Fatalf("the copied base walked by index must be admitted: %v", findings)
	}
}

// The if-converted binary search (nativegen/select.go): `hi = mid` and `lo
// = mid + 1` as selects under one compare. `csel wHi, wMid, wHi, hi` keeps
// hi at most the length — both sources are (Oak.Assembler.select_upper) —
// so the next iteration's midpoint read is admitted.
func TestCheckSelectKeepsUpperBound(t *testing.T) {
	decl := "search: (keys: []u64, target: u64) -> u32"
	body := "  bind x0, w1 = keys\n  bind x2 = target\n  clobber x9, x10, x11, x12, x13\n  mov w9, wzr\n  mov w10, w1\nloop:\n  cmp w9, w10\n  b.hs done\n  sub w11, w10, w9\n  lsr w11, w11, #1\n  add w12, w9, w11\n  ldr x11, [x0, w12, uxtw #3]\n  add w13, w12, #1\n  cmp x11, x2\n  csel w9, w13, w9, lo\n  csel w10, w12, w10, hi\n  b loop\ndone:\n  mov w0, w9\n  ret"
	if findings := checkBody(t, decl, body); len(findings) != 0 {
		t.Fatalf("the select-form search must be admitted: %v", findings)
	}
	// A select whose other source is unbounded is not a bound.
	unbounded := strings.Replace(body, "  csel w10, w12, w10, hi\n", "  csel w10, w12, w13, hi\n", 1)
	findings := checkBody(t, decl, unbounded)
	if len(findings) == 0 || !strings.Contains(findings[0], "not this span's length register") {
		t.Fatalf("hi selected from mid + 1 is not below the length, got %v", findings)
	}
}

// The if-converted increment forms (nativegen/select.go): `csinc wD, wCur,
// wzr, !cond` is `cond ? 1 : cur` and `cinc wD, wCur, cond` is `cond ? cur
// + 1 : cur`; the verifier reads both as the Oak conditional.
func TestVerifyConditionalIncrements(t *testing.T) {
	set := verifyCase(t, "flag_set: (v: u32, f: u32) -> u32", "{\n  v == u32(0) ? { u32(1) } | { f }\n}", "  bind w0 = v\n  bind w1 = f\n  cmp w0, #0\n  csinc w0, w1, wzr, ne\n  ret")
	if set.Kind != VerdictProven {
		t.Fatalf("csinc from wzr must be proven as the conditional one, got %s: %s", set.Kind, set.Message)
	}
	wrong := verifyCase(t, "flag_set: (v: u32, f: u32) -> u32", "{\n  v == u32(0) ? { u32(1) } | { f }\n}", "  bind w0 = v\n  bind w1 = f\n  cmp w0, #0\n  csinc w0, w1, wzr, eq\n  ret")
	if wrong.Kind == VerdictProven {
		t.Fatal("the inverted condition must be refuted")
	}
	inc := verifyCase(t, "count: (v: u32, n: u32) -> u32", "{\n  v == u32(0) ? { n + u32(1) } | { n }\n}", "  bind w0 = v\n  bind w1 = n\n  cmp w0, #0\n  cinc w0, w1, eq\n  ret")
	if inc.Kind != VerdictProven {
		t.Fatalf("cinc must be proven as the conditional increment, got %s: %s", inc.Kind, inc.Message)
	}
}
