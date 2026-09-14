package asm

import "testing"

// Variable shift counts (docs/spec/94-assembler.md §8, variable shift
// counts): Oak traps at the width and so does the native code — `cmp wN,
// #width; b.hs trap` before the register shift — so the equivalence is
// over the counts below the width, where the guarded machine shift is
// Oak's. A narrow operand shifts in a w register and is masked back; on
// the dropped counts the lowered term is the machine's value, so no
// mismatch is invented there (Oak.Shifts). The other direction of the
// shift is refuted.
func TestVerifyVariableShift(t *testing.T) {
	word := "  bind w0 = x\n  bind w1 = n\n  clobber x9, x10, x1\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w9, w0\n  mov w10, w1\n  cmp w10, #32\n  b.hs trap_3\n  lsl w9, w9, w10\n  mov w0, w9\nret_2:\n  add sp, sp, #80\n  ret\ntrap_3:\n  brk #1"
	if v := verifyCase(t, "shl32: (x: u32, n: u32) -> u32", "x << n", word); v.Kind != VerdictProven {
		t.Fatalf("shl32 must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "shl32: (x: u32, n: u32) -> u32", "x >> n", word); v.Kind != VerdictMismatch {
		t.Fatalf("a right shift against lsl must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	byte := "  bind w0 = x\n  bind w1 = n\n  clobber x9, x10, x1\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w9, w0\n  mov w10, w1\n  cmp w10, #8\n  b.hs trap_3\n  lsl w9, w9, w10\n  and w9, w9, #255\n  mov w0, w9\nret_2:\n  add sp, sp, #80\n  ret\ntrap_3:\n  brk #1"
	if v := verifyCase(t, "shl8: (x: u8, n: u8) -> u8", "x << n", byte); v.Kind != VerdictProven {
		t.Fatalf("shl8 must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A signed operand keeps the refusal: the backends leave it to C.
	if v := verifyCase(t, "shl8: (x: i8, n: i8) -> i8", "x << n", byte); v.Kind != VerdictTrusted {
		t.Fatalf("a signed variable shift must stay trusted, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: sllw for a 32-bit operand, sll at XLEN with the mask
// back for a byte, both under `bgeu n, width, trap`.
func TestRV64VerifyVariableShift(t *testing.T) {
	word := "  bind a0 = x\n  bind a1 = n\n  clobber t0, t1, t2\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  mv s1, a0\n  mv s2, a1\nhead_1:\n  mv t0, s1\n  mv t1, s2\n  li t2, 32\n  bgeu t1, t2, trap_3\n  sllw t0, t0, t1\n  mv a0, t0\nret_2:\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap_3:\n  ebreak"
	if v := rv64Verify(t, "shl32: (x: u32, n: u32) -> u32", "x << n", word); v.Kind != VerdictProven {
		t.Fatalf("shl32 must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "shl32: (x: u32, n: u32) -> u32", "x >> n", word); v.Kind != VerdictMismatch {
		t.Fatalf("a right shift against sllw must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	byte := "  bind a0 = x\n  bind a1 = n\n  clobber t0, t1, t2\n  frame 96\n  addi sp, sp, -96\n  sd s1, 0(sp)\n  sd s2, 8(sp)\n  mv s1, a0\n  mv s2, a1\nhead_1:\n  mv t0, s1\n  mv t1, s2\n  li t2, 8\n  bgeu t1, t2, trap_3\n  sll t0, t0, t1\n  andi t0, t0, 255\n  mv a0, t0\nret_2:\n  ld s1, 0(sp)\n  ld s2, 8(sp)\n  addi sp, sp, 96\n  ret\ntrap_3:\n  ebreak"
	if v := rv64Verify(t, "shl8: (x: u8, n: u8) -> u8", "x << n", byte); v.Kind != VerdictProven {
		t.Fatalf("shl8 must be proven, got %s: %s", v.Kind, v.Message)
	}
}
