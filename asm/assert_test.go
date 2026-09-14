package asm

import "testing"

// An assert in a verified body (docs/spec/94-assembler.md §8, thirty-second
// increment): the lowering's `cbz <cond>, trap` is a trap arm the executor
// drops, and the Oak side leaves the assert out likewise, so the two sides
// are compared on the paths where the assert held.
func TestVerifyAssert(t *testing.T) {
	decl := "check_all: (a, b: u32) -> u32"
	body := "  bind w0 = a\n  bind w1 = b\n  clobber x9\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  cmp w0, #100\n  cset w9, lo\n  cbz w9, trap_3\n  cmp w1, #100\n  cset w9, lo\n  cbz w9, trap_3\n  add w9, w0, w1\n  mov w0, w9\nret_2:\n  add sp, sp, #80\n  ret\ntrap_3:\n  brk #1"
	if v := verifyCase(t, decl, "{\n  assert(a < u32(100))\n  assert(b < u32(100))\n  a + b\n}", body); v.Kind != VerdictProven {
		t.Fatalf("a body with asserts must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, "{\n  assert(a < u32(100))\n  assert(b < u32(100))\n  a - b\n}", body); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong result after the asserts must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

func TestRV64VerifyAssert(t *testing.T) {
	decl := "check_all: (a, b: u32) -> u32"
	body := "  bind a0 = a\n  bind a1 = b\n  clobber t0, t1\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  mv s1, a0\n  mv s2, a1\nhead_1:\n  mv t0, s1\n  li t1, 100\n  sltu t0, t0, t1\n  beqz t0, trap_3\n  mv t0, s2\n  li t1, 100\n  sltu t0, t0, t1\n  beqz t0, trap_3\n  mv t0, s1\n  mv t1, s2\n  addw t0, t0, t1\n  mv a0, t0\nret_2:\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap_3:\n  ebreak"
	if v := rv64Verify(t, decl, "{\n  assert(a < u32(100))\n  assert(b < u32(100))\n  a + b\n}", body); v.Kind != VerdictProven {
		t.Fatalf("a body with asserts must be proven, got %s: %s", v.Kind, v.Message)
	}
}
