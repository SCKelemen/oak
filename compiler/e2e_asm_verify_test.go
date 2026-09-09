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
