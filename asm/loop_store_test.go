package asm

import (
	"strings"
	"testing"
)

// Stores in data-dependent loops (docs/spec/94-assembler.md §8, thirty-first
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
	// A body that reads the span it stores to reads the loop's memory at
	// the start of the iteration, a fresh memory shared by both sides.
	reading := "  bind x0, w1 = s\n  bind w2 = x\n  clobber x9, x10, x2, x3\n  frame 80\n  sub sp, sp, #80\nhead_1:\n  mov w3, wzr\nloop_4:\n  cmp w3, w1\n  b.hs done_5\n  ldrh w9, [x0, w3, uxtw #1]\n  add w10, w2, w9\n  strh w10, [x0, w3, uxtw #1]\n  add w3, w3, #1\n  b loop_4\ndone_5:\nret_2:\n  add sp, sp, #80\n  ret"
	if v := verifyCase(t, decl, fillBody("s[i] = x + s[i]"), reading); v.Kind != VerdictProven {
		t.Fatalf("a body reading the span it stores to must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, fillBody("s[i] = x - s[i]"), reading); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong in-place value must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// In-place loops: the native lowering of `v[i] = v[i] * k` and of the
// running sum `v[i] = v[i] + v[i - 1]`, which reads the element the
// previous iteration wrote — the loop's memory carries it.
func TestVerifyLoopStoresInPlace(t *testing.T) {
	scale := `  bind x0, w1 = v
  bind w2 = k
  clobber x9, x2, x3
  frame 80
  sub sp, sp, #80
head_1:
  mov w3, wzr
loop_4:
  cmp w3, w1
  b.hs done_5
  ldr w9, [x0, w3, uxtw #2]
  mul w9, w9, w2
  str w9, [x0, w3, uxtw #2]
  add w3, w3, #1
  b loop_4
done_5:
ret_2:
  add sp, sp, #80
  ret`
	decl := "scale_in_place: (v: [*]u32, k: u32) -> ()"
	body := func(store string) string {
		return "{\n  i: u32 = u32(0)\n  while i < len(v) {\n    " + store + "\n    i = i + u32(1)\n  }\n}"
	}
	if v := verifyCase(t, decl, body("v[i] = v[i] * k"), scale); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory it writes (v)") {
		t.Fatalf("scale_in_place must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, decl, body("v[i] = v[i] + k"), scale); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong in-place operation must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	running := `  bind x0, w1 = v
  clobber x9, x10, x2
  frame 80
  sub sp, sp, #80
head_1:
  movz w2, #1
loop_4:
  cmp w2, w1
  b.hs done_5
  cmp w2, w1
  b.hs trap_3
  ldr w9, [x0, w2, uxtw #2]
  sub w10, w2, #1
  cmp w10, w1
  b.hs trap_3
  ldr w10, [x0, w10, uxtw #2]
  add w9, w9, w10
  cmp w2, w1
  b.hs trap_3
  str w9, [x0, w2, uxtw #2]
  add w2, w2, #1
  b loop_4
done_5:
ret_2:
  add sp, sp, #80
  ret
trap_3:
  brk #1`
	runDecl := "running: (v: [*]u32) -> ()"
	runBody := func(store string) string {
		return "{\n  i: u32 = u32(1)\n  while i < len(v) {\n    " + store + "\n    i = i + u32(1)\n  }\n}"
	}
	if v := verifyCase(t, runDecl, runBody("v[i] = v[i] + v[i - u32(1)]"), running); v.Kind != VerdictProven {
		t.Fatalf("the running sum must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, runDecl, runBody("v[i] = v[i] - v[i - u32(1)]"), running); v.Kind != VerdictMismatch {
		t.Fatalf("the running difference against the sum must be a mismatch, got %s: %s", v.Kind, v.Message)
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
	// In place: the element read through the loop's memory, then stored.
	scale := `  bind a0, a1 = v
  bind a2 = k
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
  mv t0, s2
  slli t0, t0, 32
  srli t0, t0, 32
  bgeu t0, a3, trap_3
  slli t0, t0, 2
  add t0, a0, t0
  lw t0, 0(t0)
  mv t1, s1
  mulw t0, t0, t1
  mv t1, s2
  slli t1, t1, 32
  srli t1, t1, 32
  bgeu t1, a3, trap_3
  slli t1, t1, 2
  add t1, a0, t1
  sw t0, 0(t1)
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
	scaleDecl := "scale_in_place: (v: [*]u32, k: u32) -> ()"
	scaleBody := func(store string) string {
		return "{\n  i: u32 = u32(0)\n  while i < len(v) {\n    " + store + "\n    i = i + u32(1)\n  }\n}"
	}
	if v := rv64Verify(t, scaleDecl, scaleBody("v[i] = v[i] * k"), scale); v.Kind != VerdictProven {
		t.Fatalf("scale_in_place must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, scaleDecl, scaleBody("v[i] = v[i] + k"), scale); v.Kind != VerdictMismatch {
		t.Fatalf("the wrong in-place operation must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	running := `  bind a0, a1 = v
  clobber t0, t1, t2, a2
  frame 96
  addi sp, sp, -96
  sd s1, 0(sp)
  slli a2, a1, 32
  srli a2, a2, 32
head_1:
  li t0, 1
  mv s1, t0
loop_4:
  sext.w t0, a2
  bgeu s1, t0, done_5
  mv t0, s1
  slli t0, t0, 32
  srli t0, t0, 32
  bgeu t0, a2, trap_3
  slli t0, t0, 2
  add t0, a0, t0
  lw t0, 0(t0)
  mv t1, s1
  li t2, 1
  subw t1, t1, t2
  slli t1, t1, 32
  srli t1, t1, 32
  bgeu t1, a2, trap_3
  slli t1, t1, 2
  add t1, a0, t1
  lw t1, 0(t1)
  addw t0, t0, t1
  mv t1, s1
  slli t1, t1, 32
  srli t1, t1, 32
  bgeu t1, a2, trap_3
  slli t1, t1, 2
  add t1, a0, t1
  sw t0, 0(t1)
  mv t0, s1
  li t1, 1
  addw t0, t0, t1
  mv s1, t0
  j loop_4
done_5:
ret_2:
  ld s1, 0(sp)
  addi sp, sp, 96
  ret
trap_3:
  ebreak`
	runDecl := "running: (v: [*]u32) -> ()"
	runBody := func(store string) string {
		return "{\n  i: u32 = u32(1)\n  while i < len(v) {\n    " + store + "\n    i = i + u32(1)\n  }\n}"
	}
	if v := rv64Verify(t, runDecl, runBody("v[i] = v[i] + v[i - u32(1)]"), running); v.Kind != VerdictProven {
		t.Fatalf("the running sum must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, runDecl, runBody("v[i] = v[i] - v[i - u32(1)]"), running); v.Kind != VerdictMismatch {
		t.Fatalf("the running difference against the sum must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// A body that stores and then forks: the store before the fork is the
// same entry on every path and stays unconditional; the native lowering
// of mark_bits on both lanes.
func TestVerifyLoopStoresForkedBody(t *testing.T) {
	oak := "{\n  count: u32 = u32(0)\n  bits: u32 = lanes\n  while bits != u32(0) && count < len(marks) {\n    marks[count] = bits\n    count = count + u32(1)\n    (bits & u32(1)) == u32(1) ? { count = count + u32(0) }\n    bits = bits >> u32(1)\n  }\n  count\n}"
	decl := "mark_bits: (marks: [*]u32, lanes: u32) -> u32"
	arm := `  bind x0, w1 = marks
  bind w2 = lanes
  clobber x9, x19, x20, x2, x3, x4
  frame 80
  sub sp, sp, #80
  stp x19, x20, [sp]
  mov x19, x0
  mov w20, w1
head_1:
  mov w3, wzr
  mov w4, w2
loop_4:
  cmp w4, #0
  b.eq done_5
  cmp w3, w20
  b.hs done_5
  mov w9, w4
  str w9, [x19, w3, uxtw #2]
  add w3, w3, #1
  and w9, w4, #1
  cmp w9, #1
  cset w9, eq
  cbz w9, else_6
  add w3, w3, #0
  b endif_7
else_6:
endif_7:
  lsr w4, w4, #1
  b loop_4
done_5:
  mov w9, w3
  mov w0, w9
ret_2:
  ldp x19, x20, [sp]
  add sp, sp, #80
  ret`
	if v := verifyCase(t, decl, oak, arm); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory it writes (marks)") {
		t.Fatalf("mark_bits must be proven in the span memory, got %s: %s", v.Kind, v.Message)
	}
	rv := `  bind a0, a1 = marks
  bind a2 = lanes
  clobber t0, t1, t2, a3
  frame 96
  addi sp, sp, -96
  sd s1, 0(sp)
  sd s2, 8(sp)
  sd s4, 24(sp)
  sd s5, 32(sp)
  sd s6, 40(sp)
  mv s1, a0
  mv s2, a1
  slli a3, s2, 32
  srli a3, a3, 32
  mv s4, a2
head_1:
  li t0, 0
  mv s5, t0
  mv t0, s4
  mv s6, t0
loop_4:
  mv t1, s6
  li t2, 0
  sub t1, t1, t2
  sltu t1, zero, t1
  mv t0, t1
  beqz t0, short_6
  mv t1, s5
  sext.w t2, a3
  sltu t1, t1, t2
  mv t0, t1
short_6:
  beqz t0, done_5
  mv t0, s6
  mv t1, s5
  slli t1, t1, 32
  srli t1, t1, 32
  bgeu t1, a3, trap_3
  slli t1, t1, 2
  add t1, s1, t1
  sw t0, 0(t1)
  mv t0, s5
  li t1, 1
  addw t0, t0, t1
  mv s5, t0
  mv t0, s6
  li t1, 1
  and t0, t0, t1
  li t1, 1
  bne t0, t1, else_7
  mv t1, s5
  li t0, 0
  addw t1, t1, t0
  mv s5, t1
  j endif_8
else_7:
endif_8:
  mv t1, s6
  srliw t1, t1, 1
  mv s6, t1
  j loop_4
done_5:
  mv t1, s5
  mv a0, t1
ret_2:
  ld s1, 0(sp)
  ld s2, 8(sp)
  ld s4, 24(sp)
  ld s5, 32(sp)
  ld s6, 40(sp)
  addi sp, sp, 96
  ret
trap_3:
  ebreak`
	if v := rv64Verify(t, decl, oak, rv); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory it writes (marks)") {
		t.Fatalf("mark_bits on RV64 must be proven in the span memory, got %s: %s", v.Kind, v.Message)
	}
}
