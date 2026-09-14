package asm

import (
	"strings"
	"testing"
)

// Integer division and remainder as uninterpreted operations of the
// operands (docs/spec/94-assembler.md §8, thirty-first increment): the
// quotient is one function on both sides, the remainder a - (a / b) * b —
// the AArch64 lowering's sdiv/udiv then msub, RISC-V's rem/remu, Oak's %
// — so the native `divmod`, `quot`, and `rem` are proven; a zero divisor
// traps on both sides. Swapped operands are refuted on a concrete input.
func TestVerifyDivision(t *testing.T) {
	divmod := `  bind w0 = a
  bind w1 = b
  clobber x9, x10, x11, x12, x1
  frame 80
  sub sp, sp, #80
head_1:
  mov w9, w0
  mov w10, w1
  cbz w10, trap_3
  sdiv w9, w9, w10
  movz w10, #100
  mul w9, w9, w10
  mov w10, w0
  mov w11, w1
  cbz w11, trap_3
  sdiv w12, w10, w11
  msub w10, w12, w11, w10
  add w9, w9, w10
  mov w0, w9
ret_2:
  add sp, sp, #80
  ret
trap_3:
  brk #1`
	decl := "divmod: (a: i32, b: i32) -> i32"
	if v := verifyCase(t, decl, "(a / b) * i32(100) + a % b", divmod); v.Kind != VerdictProven {
		t.Fatalf("divmod must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, "(b / a) * i32(100) + a % b", divmod); v.Kind != VerdictMismatch {
		t.Fatalf("swapped division operands must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	quot := "  bind w0 = a\n  bind w1 = b\n  clobber x9, x10, x1\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w9, w0\n  mov w10, w1\n  cbz w10, trap_3\n  udiv w9, w9, w10\n  mov w0, w9\nret_2:\n  add sp, sp, #80\n  ret\ntrap_3:\n  brk #1"
	if v := verifyCase(t, "quot: (a, b: u32) -> u32", "a / b", quot); v.Kind != VerdictProven {
		t.Fatalf("quot must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Signed against unsigned division is another operation.
	if v := verifyCase(t, "quot: (a, b: i32) -> i32", "a / b", quot); v.Kind != VerdictMismatch {
		t.Fatalf("signed division against udiv must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	rem := "  bind w0 = a\n  bind w1 = b\n  clobber x9, x10, x11, x1\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w9, w0\n  mov w10, w1\n  cbz w10, trap_3\n  udiv w11, w9, w10\n  msub w9, w11, w10, w9\n  mov w0, w9\nret_2:\n  add sp, sp, #80\n  ret\ntrap_3:\n  brk #1"
	v := verifyCase(t, "rem: (a, b: u32) -> u32", "a % b", rem)
	if v.Kind != VerdictProven {
		t.Fatalf("rem must be proven, got %s: %s", v.Kind, v.Message)
	}
	if !strings.Contains(v.Message, "proven") {
		t.Fatalf("unexpected message %q", v.Message)
	}
}

// The RV64 lane: divw/remw and divuw/remuw as the same terms.
func TestRV64VerifyDivision(t *testing.T) {
	divmod := `  bind a0 = a
  bind a1 = b
  clobber t0, t1, t2
  frame 96
  addi sp, sp, -96
  sd s1, 0(sp)
  sd s2, 8(sp)
  mv s1, a0
  mv s2, a1
head_1:
  mv t0, s1
  mv t1, s2
  beqz t1, trap_3
  divw t0, t0, t1
  li t1, 100
  mulw t0, t0, t1
  mv t1, s1
  mv t2, s2
  beqz t2, trap_3
  remw t1, t1, t2
  addw t0, t0, t1
  mv a0, t0
ret_2:
  ld s1, 0(sp)
  ld s2, 8(sp)
  addi sp, sp, 96
  ret
trap_3:
  ebreak`
	decl := "divmod: (a: i32, b: i32) -> i32"
	if v := rv64Verify(t, decl, "(a / b) * i32(100) + a % b", divmod); v.Kind != VerdictProven {
		t.Fatalf("divmod must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "(b / a) * i32(100) + a % b", divmod); v.Kind != VerdictMismatch {
		t.Fatalf("swapped division operands must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	rem := "  bind a0 = a\n  bind a1 = b\n  clobber t0, t1\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  mv s1, a0\n  mv s2, a1\nhead_1:\n  mv t0, s1\n  mv t1, s2\n  beqz t1, trap_3\n  remuw t0, t0, t1\n  mv a0, t0\nret_2:\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap_3:\n  ebreak"
	if v := rv64Verify(t, "rem: (a, b: u32) -> u32", "a % b", rem); v.Kind != VerdictProven {
		t.Fatalf("rem must be proven, got %s: %s", v.Kind, v.Message)
	}
	quot := "  bind a0 = a\n  bind a1 = b\n  clobber t0, t1\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  mv s1, a0\n  mv s2, a1\nhead_1:\n  mv t0, s1\n  mv t1, s2\n  beqz t1, trap_3\n  divuw t0, t0, t1\n  mv a0, t0\nret_2:\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap_3:\n  ebreak"
	if v := rv64Verify(t, "quot: (a, b: u32) -> u32", "a / b", quot); v.Kind != VerdictProven {
		t.Fatalf("quot must be proven, got %s: %s", v.Kind, v.Message)
	}
}
