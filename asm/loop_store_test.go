package asm

import (
	"strings"
	"testing"
)

// Stores in data-dependent loops (docs/spec/94-assembler.md §8, thirtieth
// increment): a counting loop that stores one element per iteration is
// proven through the coupling — each iteration's store reaches the same
// element with the same value on both sides — and refuted on concrete
// inputs when it does not. The native lowering of `fill` and `fill_f64`.
const fillArm = `  bind x0, w1 = s
  bind w2 = x
  clobber x9, x10, x2, x3
  frame 80
  sub sp, sp, #80
  and w2, w2, #65535
head_1:
  mov w3, wzr
loop_4:
  cmp w3, w1
  b.hs done_5
  mov w9, w3
  and w9, w9, #65535
  add w10, w2, w9
  and w10, w10, #65535
  strh w10, [x0, w3, uxtw #1]
  add w3, w3, #1
  b loop_4
done_5:
ret_2:
  add sp, sp, #80
  ret`

const fillF64Arm = `  bind x0, w1 = s
  bind d0 = x
  clobber x9, d16, d17, d8, x2
  frame 144
  sub sp, sp, #144
  str d8, [sp, #80]
  fmov d8, d0
head_1:
  mov w2, wzr
loop_4:
  cmp w2, w1
  b.hs done_5
  fmov d16, d8
  mov w9, w2
  scvtf d17, w9
  fadd d16, d16, d17
  str d16, [x0, w2, uxtw #3]
  add w2, w2, #1
  b loop_4
done_5:
ret_2:
  ldr d8, [sp, #80]
  add sp, sp, #144
  ret`

func fillBody(store string) string {
	return "{\n  i: u32 = u32(0)\n  while i < len(s) {\n    " + store + "\n    i = i + u32(1)\n  }\n}"
}

func TestVerifyLoopStores(t *testing.T) {
	decl := "fill: (s: [*]u16, x: u16) -> ()"
	proven := verifyCase(t, decl, fillBody("s[i] = x + u16_trunc_u32(i)"), fillArm)
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "span memory it writes (s)") {
		t.Fatalf("fill must be proven in the span memory, got %s: %s", proven.Kind, proven.Message)
	}
	// A wrong value or a wrong element is refuted by a concrete input.
	if v := verifyCase(t, decl, fillBody("s[i] = x - u16_trunc_u32(i)"), fillArm); v.Kind != VerdictMismatch || !strings.Contains(v.Message, "leaves") {
		t.Fatalf("the wrong stored value must be a mismatch naming the element, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, fillBody("s[len(s) - u32(1) - i] = x + u16_trunc_u32(i)"), fillArm); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong element must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// The float fill: the accumulator in d8, the conversion of the counter.
	f64 := "fill_f64: (s: [*]f64, x: f64) -> ()"
	if v := verifyCase(t, f64, fillBody("s[i] = x + f64_round_i32(i32_bits_u32(i))"), fillF64Arm); v.Kind != VerdictProven {
		t.Fatalf("fill_f64 must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, f64, fillBody("s[i] = x - f64_round_i32(i32_bits_u32(i))"), fillF64Arm); v.Kind != VerdictMismatch {
		t.Fatalf("fill_f64 with a difference must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// A body that reads the span it stores to is outside the summary: the
	// summary carries registers, not memories.
	reading := "  bind x0, w1 = s\n  bind w2 = x\n  clobber x9, x10, x2, x3\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w3, wzr\nloop_4:\n  cmp w3, w1\n  b.hs done_5\n  ldrh w9, [x0, w3, uxtw #1]\n  add w10, w2, w9\n  strh w10, [x0, w3, uxtw #1]\n  add w3, w3, #1\n  b loop_4\ndone_5:\nret_2:\n  add sp, sp, #80\n  ret"
	if v := verifyCase(t, decl, fillBody("s[i] = x + s[i]"), reading); v.Kind != VerdictTrusted || !strings.Contains(v.Message, "reading the span s it stores to") {
		t.Fatalf("a body reading the span it stores to must stay trusted with the reason, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: the store through the guarded element address, the
// counter widened by addw, the float fill through fsd.
func TestRV64VerifyLoopStores(t *testing.T) {
	fill := `  bind a0, a1 = s
  bind a2 = x
  clobber t0, t1, a3
  frame 96
  addi sp, sp, -96
  sd s1, 0(sp)
  sd s2, 8(sp)
  slli a3, a1, 32
  srli a3, a3, 32
  mv s1, a2
head_1:
  li t0, 0
  mv s2, t0
loop_4:
  sext.w t0, a3
  bgeu s2, t0, done_5
  mv t0, s1
  mv t1, s2
  slli t1, t1, 48
  srli t1, t1, 48
  add t0, t0, t1
  slli t0, t0, 48
  srli t0, t0, 48
  mv t1, s2
  slli t1, t1, 32
  srli t1, t1, 32
  bgeu t1, a3, trap_3
  slli t1, t1, 1
  add t1, a0, t1
  sh t0, 0(t1)
  mv t0, s2
  li t1, 1
  addw t0, t0, t1
  mv s2, t0
  j loop_4
done_5:
ret_2:
  ld s1, 0(sp)
  ld s2, 8(sp)
  addi sp, sp, 96
  ret
trap_3:
  ebreak`
	decl := "fill: (s: [*]u16, x: u16) -> ()"
	if v := rv64Verify(t, decl, fillBody("s[i] = x + u16_trunc_u32(i)"), fill); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory it writes (s)") {
		t.Fatalf("fill must be proven in the span memory, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, fillBody("s[i] = x - u16_trunc_u32(i)"), fill); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong stored value must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	fillF64 := `  bind a0, a1 = s
  bind fa0 = x
  clobber t0, t1, a2, ft0, ft1
  frame 192
  addi sp, sp, -192
  sd s1, 0(sp)
  fsd fs0, 88(sp)
  slli a2, a1, 32
  srli a2, a2, 32
  fsgnj.d fs0, fa0, fa0
head_1:
  li t0, 0
  mv s1, t0
loop_4:
  sext.w t0, a2
  bgeu s1, t0, done_5
  fsgnj.d ft0, fs0, fs0
  mv t0, s1
  fcvt.d.w ft1, t0
  fadd.d ft0, ft0, ft1
  mv t0, s1
  slli t0, t0, 32
  srli t0, t0, 32
  bgeu t0, a2, trap_3
  slli t0, t0, 3
  add t0, a0, t0
  fsd ft0, 0(t0)
  mv t0, s1
  li t1, 1
  addw t0, t0, t1
  mv s1, t0
  j loop_4
done_5:
ret_2:
  fld fs0, 88(sp)
  ld s1, 0(sp)
  addi sp, sp, 192
  ret
trap_3:
  ebreak`
	f64 := "fill_f64: (s: [*]f64, x: f64) -> ()"
	if v := rv64Verify(t, f64, fillBody("s[i] = x + f64_round_i32(i32_bits_u32(i))"), fillF64); v.Kind != VerdictProven {
		t.Fatalf("fill_f64 must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, f64, fillBody("s[i] = x - f64_round_i32(i32_bits_u32(i))"), fillF64); v.Kind != VerdictMismatch {
		t.Fatalf("fill_f64 with a difference must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
