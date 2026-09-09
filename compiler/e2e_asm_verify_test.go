package compiler

import (
	"strings"
	"testing"
)

// §8 verification at the asm gate: a wrong body never compiles; a proven
// body compiles and executes on both realizations.
func TestAsmVerificationRejectsMismatch(t *testing.T) {
	_, err := New().WithSource("wrong.oak", `
add_asm: (left, right: u32) -> u32 = left + right

main: (): i32 {
  assert(add_asm(u32(40), u32(2)) == u32(42))
  42
}
`).WithAsmUnit("wrong.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  bind w0 = left
  bind w1 = right
  sub w0, w0, w1
  ret
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "disagrees with its Oak body") {
		t.Fatalf("a body disagreeing with its Oak specification must be rejected, got %v", err)
	}
}

func TestE2EAsmVerifiedFallbackExecutesBothWays(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("verified.oak", `
scale: (a: u64) -> u64 = (a + u64(2)) << 3

main: (): i32 {
  assert(scale(u64(3)) == u64(40))
  42
}
`).WithAsmUnit("scale.arm64.oakasm", `
scale: (a: u64) -> u64 = {
  bind x0 = a
  clobber x9
  add x9, x0, #2
  lsl x0, x9, #3
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
}

// A conditional body: the Oak `a < b ? b | a` is the specification of a
// cmp/csel pair; proven at the asm gate, then executed both ways.
func TestE2EAsmVerifiedConditionalExecutesBothWays(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("max.oak", `
max32: (a, b: u32) -> u32 = a < b ? b | a

main: (): i32 {
  assert(max32(u32(40), u32(2)) == u32(40))
  assert(max32(u32(2), u32(42)) == u32(42))
  assert(max32(u32(7), u32(7)) == u32(7))
  42
}
`).WithAsmUnit("max.arm64.oakasm", `
max32: (a, b: u32) -> u32 = {
  bind w0 = a
  bind w1 = b
  cmp w0, w1
  csel w0, w1, w0, lo
  ret
}
`)
	for _, flags := range [][]string{nil, {"-DOAK_PORTABLE_INTRINSICS"}} {
		_, code, abnormal := buildAndRunFrom(t, "verified_cond", comp, flags...)
		if abnormal || code != 42 {
			t.Fatalf("flags %v: exit = (%d, abnormal=%v), want 42", flags, code, abnormal)
		}
	}
	// The wrong condition never compiles.
	_, err := New().WithSource("max.oak", `
max32: (a, b: u32) -> u32 = a < b ? b | a

main: (): i32 {
  assert(max32(u32(1), u32(2)) == u32(2))
  42
}
`).WithAsmUnit("max.arm64.oakasm", `
max32: (a, b: u32) -> u32 = {
  bind w0 = a
  bind w1 = b
  cmp w0, w1
  csel w0, w1, w0, hi
  ret
}
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "disagrees with its Oak body") {
		t.Fatalf("csel hi for a < b must be rejected at the gate, got %v", err)
	}
}
