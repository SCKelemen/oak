package compiler

import "testing"

// The spec's own first example (docs/spec/94-assembler.md §2), executed:
// the operand-stack shorthand desugars to checked bound-register code.
func TestE2EAsmOperandStackShorthand(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("stack.oak", `
add_asm: (left, right: u32) -> u32
scale: (a: u64) -> u64

main: (): i32 {
  assert(add_asm(u32(40), u32(2)) == u32(42))
  assert(scale(u64(3)) == u64(40))
  42
}
`).WithAsmUnit("stack.arm64.oakasm", `
add_asm: (left, right: u32) -> u32 = {
  push left
  push right
  add
}

scale: (a: u64) -> u64 = {
  push a
  push #2
  add
  push #3
  lsl
}
`)
	_, code, abnormal := buildAndRunFrom(t, "stack", comp)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
