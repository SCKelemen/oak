package asm

import (
	"strings"
	"testing"
)

// A float span reduction in a loop body (docs/spec/94-assembler.md §8,
// floats in loop bodies): the element loads through the s view (`ldr sN,
// [xB, wI, uxtw #2]`), the accumulator loop-carried in the low lane of
// d8, the Oak local paired with it zero-extended. The lowering the native
// backend emits for `total` is proven; the operand order of the sum is
// checked (no commutativity is assumed of the uninterpreted fadd).
func TestVerifyFloatLoop(t *testing.T) {
	decl := "total: (v: []f32) -> f32"
	body := `  bind x0, w1 = v
  clobber x9, x19, x20, d16, d17, d8, x2
  frame 144
  sub sp, sp, #144
  stp x19, x20, [sp]
  str d8, [sp, #80]
  mov x19, x0
  mov w20, w1
head_1:
  mov w9, wzr
  fmov s16, w9
  fmov s8, s16
  mov w2, wzr
loop_4:
  cmp w2, w20
  b.hs done_5
  fmov s16, s8
  ldr s17, [x19, w2, uxtw #2]
  fadd s16, s16, s17
  fmov s8, s16
  add w2, w2, #1
  b loop_4
done_5:
  fmov s16, s8
  fmov s0, s16
ret_2:
  ldr d8, [sp, #80]
  ldp x19, x20, [sp]
  add sp, sp, #144
  ret`
	oak := func(sum string) string {
		return "{\n  acc: f32 = 0.0\n  i: u32 = u32(0)\n  while i < len(v) {\n    acc = " + sum + "\n    i = i + u32(1)\n  }\n  acc\n}"
	}
	if v := verifyCase(t, decl, oak("acc + v[i]"), body); v.Kind != VerdictProven {
		t.Fatalf("the float reduction must be proven, got %s: %s", v.Kind, v.Message)
	}
	// The swapped sum is another application of fadd: no commutativity is
	// assumed, so the coupling is not proven — and IEEE addition commutes
	// on the witnesses (up to a NaN payload), so it is not refuted either:
	// evidence, not proof.
	if v := verifyCase(t, decl, oak("v[i] + acc"), body); v.Kind != VerdictWitnessed || !strings.Contains(v.Message, "not proven to preserve") {
		t.Fatalf("the swapped sum must be evidence only, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, oak("acc - v[i]"), body); v.Kind != VerdictMismatch {
		t.Fatalf("a difference against fadd must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: `flw` through the span element address, the accumulator
// in fs0 moved through fsgnj.d (the backend's fmv.d), the loop-carried f
// register paired with the f32 local zero-extended.
func TestRV64VerifyFloatLoop(t *testing.T) {
	decl := "total: (v: []f32) -> f32"
	body := `  bind a0, a1 = v
  clobber t0, t1, a2, ft0, ft1
  frame 192
  addi sp, sp, -192
  sd s1, 0(sp)
  sd s2, 8(sp)
  sd s4, 24(sp)
  fsd fs0, 88(sp)
  mv s1, a0
  mv s2, a1
  slli a2, s2, 32
  srli a2, a2, 32
head_1:
  li t0, 0
  fmv.w.x ft0, t0
  fsgnj.d fs0, ft0, ft0
  li t0, 0
  mv s4, t0
loop_4:
  sext.w t0, a2
  bgeu s4, t0, done_5
  fsgnj.d ft0, fs0, fs0
  mv t0, s4
  slli t0, t0, 32
  srli t0, t0, 32
  bgeu t0, a2, trap_3
  slli t0, t0, 2
  add t0, s1, t0
  flw ft1, 0(t0)
  fadd.s ft0, ft0, ft1
  fsgnj.d fs0, ft0, ft0
  mv t0, s4
  li t1, 1
  addw t0, t0, t1
  mv s4, t0
  j loop_4
done_5:
  fsgnj.d ft0, fs0, fs0
  fsgnj.d fa0, ft0, ft0
ret_2:
  fld fs0, 88(sp)
  ld s1, 0(sp)
  ld s2, 8(sp)
  ld s4, 24(sp)
  addi sp, sp, 192
  ret
trap_3:
  ebreak`
	oak := func(sum string) string {
		return "{\n  acc: f32 = 0.0\n  i: u32 = u32(0)\n  while i < len(v) {\n    acc = " + sum + "\n    i = i + u32(1)\n  }\n  acc\n}"
	}
	if v := rv64Verify(t, decl, oak("acc + v[i]"), body); v.Kind != VerdictProven {
		t.Fatalf("the float reduction must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, oak("v[i] + acc"), body); v.Kind != VerdictWitnessed {
		t.Fatalf("the swapped sum must be evidence only, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, oak("acc - v[i]"), body); v.Kind != VerdictMismatch {
		t.Fatalf("a difference against fadd.s must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Outside a loop: a float element load and store through a span.
	guarded := func(scale string, access string) string {
		return "  clobber t0, a2\n  slli a2, a1, 32\n  srli a2, a2, 32\n  li t0, 0\n  slli t0, t0, 32\n  srli t0, t0, 32\n  bgeu t0, a2, trap_1\n  slli t0, t0, " + scale + "\n  add t0, a0, t0\n  " + access + "\n  ret\ntrap_1:\n  ebreak"
	}
	if v := rv64Verify(t, "first: (v: []f64) -> f64", "v[0]", "  bind a0, a1 = v\n"+guarded("3", "fld fa0, 0(t0)")); v.Kind != VerdictProven {
		t.Fatalf("v[0] against fld must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "put: (s: [*]f32, x: f32) -> ()", "{ s[0] = x }", "  bind a0, a1 = s\n  bind fa0 = x\n"+guarded("2", "fsw fa0, 0(t0)")); v.Kind != VerdictProven {
		t.Fatalf("s[0] = x against fsw must be proven, got %s: %s", v.Kind, v.Message)
	}
}
