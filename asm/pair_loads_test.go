package asm

import (
	"strings"
	"testing"
)

// Pair loads (docs/spec/94-assembler.md §9 "Pair loads"): `ldp xA, xB, [xE,
// #off]` off a span element address `add xE, xB, wI, uxtw #3` is admitted
// by the checker through the element region the slack guard marks four
// lanes deep, and read by the verifier as two loads — the sum of four
// elements through two pairs is proven against the Oak body; a pair one
// element past the region is refused.
func TestCheckAndVerifyPairLoads(t *testing.T) {
	decl := "four: (v: []u64) -> u64"
	oak := "{\n  len(v) >= u32(4) ? { ((v[u32(0)] + v[u32(1)]) + (v[u32(2)] + v[u32(3)])) } | { u64(0) }\n}"
	body := "  bind x0, w1 = v\n  clobber x9, x10, x11, x12, x13\n  cmp w1, #4\n  b.lo none\n  mov w9, wzr\n  sub w10, w1, #4\n  cmp w9, w10\n  b.hi none\n  add x11, x0, w9, uxtw #3\n  ldp x12, x13, [x11]\n  add x12, x12, x13\n  ldp x9, x10, [x11, #16]\n  add x9, x9, x10\n  add x0, x12, x9\n  ret\nnone:\n  mov x0, xzr\n  ret"
	if findings := checkBody(t, decl, body); len(findings) != 0 {
		t.Fatalf("the pairs inside the four-element region must be admitted: %v", findings)
	}
	if verdict := verifyCase(t, decl, oak, body); verdict.Kind != VerdictProven {
		t.Fatalf("the paired sum of four must be proven, got %s: %s", verdict.Kind, verdict.Message)
	}
	past := strings.Replace(body, "  ldp x9, x10, [x11, #16]\n", "  ldp x9, x10, [x11, #24]\n", 1)
	if findings := checkBody(t, decl, past); len(findings) == 0 {
		t.Fatal("a pair reaching the fifth element must be refused")
	}
}
