package asm

import (
	"strings"
	"testing"
)

// Vector stores through spans as memory effects (docs/spec/94-assembler.md
// §8): a `str q` on AArch64 and a `vse*.v` on RV64 write one element per
// lane into the span's write log, and `simd.store_<shape>` on the Oak side
// does the same, so a unit that stores a vector is decided in the memory
// it leaves — and a load after the store reads the stored lanes.
func TestVerifyVectorSpanStore(t *testing.T) {
	decl := "bump: (b: [*]u8, i: u32) -> ()"
	oak := "{\n  simd.store_u8x16(b, i, simd.add_u8x16(simd.load_u8x16(b, i), simd.splat_u8x16(u8(1))))\n}"
	guard := `  bind x0, w1 = b
  bind w2 = i
  clobber x9, v0, v1
  cmp w1, #16
  b.lo trap
  sub w9, w1, #16
  cmp w2, w9
  b.hi trap
  ldr q0, [x0, w2, uxtw]
`
	proven := verifyCase(t, decl, oak, guard+"  movi v1.16b, #1\n  add v0.16b, v0.16b, v1.16b\n  str q0, [x0, w2, uxtw]\n  ret\ntrap:\n  brk #1")
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "span memory") {
		t.Fatalf("the vector store must be proven in the span memory, got %s: %s", proven.Kind, proven.Message)
	}
	wrong := verifyCase(t, decl, oak, guard+"  movi v1.16b, #2\n  add v0.16b, v0.16b, v1.16b\n  str q0, [x0, w2, uxtw]\n  ret\ntrap:\n  brk #1")
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("adding two for one must be a mismatch in the memory, got %s: %s", wrong.Kind, wrong.Message)
	}
	// The store forwarded to a following load: the reloaded lanes are the
	// stored ones, so the mask is all sixteen bits.
	after := "simd.movemask_u8x16(simd.eq_u8x16(simd.load_u8x16(b, i), simd.splat_u8x16(u8(1))))"
	body := "{\n  simd.store_u8x16(b, i, simd.splat_u8x16(u8(1)))\n  " + after + "\n}"
	markGuard := strings.Replace(strings.Replace(guard, "  clobber x9, v0, v1\n", "  clobber x9, x10, v0, v1\n", 1), "  ldr q0, [x0, w2, uxtw]\n", "", 1)
	forwarded := verifyCase(t, "mark: (b: [*]u8, i: u32) -> u32", body, markGuard+"  movi v0.16b, #1\n  str q0, [x0, w2, uxtw]\n  ldr q0, [x0, w2, uxtw]\n  movi v1.16b, #1\n  cmeq v0.16b, v0.16b, v1.16b\n"+movemaskSequence+"\ntrap:\n  brk #1")
	if forwarded.Kind != VerdictProven {
		t.Fatalf("a load after the vector store must read the stored lanes, got %s: %s", forwarded.Kind, forwarded.Message)
	}
	// Float lanes through an element address (the native lowering's shape).
	fdecl := "negate: (ys: []f32, out: [*]f32) -> ()"
	foak := "{\n  simd.store_f32x4(out, u32(0), simd.neg_f32x4(simd.load_f32x4(ys, u32(0))))\n}"
	fasm := `  bind x0, w1 = ys
  bind x2, w3 = out
  clobber v0
  cmp w1, #4
  b.lo trap
  cmp w3, #4
  b.lo trap
  ldr q0, [x0]
  fneg v0.4s, v0.4s
  str q0, [x2]
  ret
trap:
  brk #1`
	if v := verifyCase(t, fdecl, foak, fasm); v.Kind != VerdictProven {
		t.Fatalf("the float vector store must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, fdecl, foak, strings.Replace(fasm, "fneg v0.4s", "fabs v0.4s", 1)); v.Kind != VerdictMismatch {
		t.Fatalf("storing abs for neg must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// The same on RV64: vle/vse through the span's base under a proven length.
func TestRV64VerifyVectorSpanStore(t *testing.T) {
	decl := "bump: (b: [*]u8) -> ()"
	oak := "{\n  simd.store_u8x16(b, u32(0), simd.add_u8x16(simd.load_u8x16(b, u32(0)), simd.splat_u8x16(u8(1))))\n}"
	head := `  bind a0, a1 = b
  clobber t0, t1, v8, v9
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 16
  bltu t1, t0, trap
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (a0)
`
	tail := "  vse8.v v8, (a0)\n  ret\ntrap:\n  ebreak"
	if v := rv64Verify(t, decl, oak, head+"  li t0, 1\n  vmv.v.x v9, t0\n  vadd.vv v8, v8, v9\n"+tail); v.Kind != VerdictProven || !strings.Contains(v.Message, "span memory") {
		t.Fatalf("the RV64 vector store must be proven in the span memory, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, oak, head+"  li t0, 2\n  vmv.v.x v9, t0\n  vadd.vv v8, v8, v9\n"+tail); v.Kind != VerdictMismatch {
		t.Fatalf("adding two for one must be a mismatch on RV64, got %s: %s", v.Kind, v.Message)
	}
	fdecl := "negate: (ys: []f32, out: [*]f32) -> ()"
	foak := "{\n  simd.store_f32x4(out, u32(0), simd.neg_f32x4(simd.load_f32x4(ys, u32(0))))\n}"
	fasm := `  bind a0, a1 = ys
  bind a2, a3 = out
  clobber t0, t1, t2, v8
  slli t1, a1, 32
  srli t1, t1, 32
  slli t2, a3, 32
  srli t2, t2, 32
  li t0, 4
  bltu t1, t0, trap
  bltu t2, t0, trap
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v8, (a0)
  vfsgnjn.vv v8, v8, v8
  vse32.v v8, (a2)
  ret
trap:
  ebreak`
	if v := rv64Verify(t, fdecl, foak, fasm); v.Kind != VerdictProven {
		t.Fatalf("the RV64 float vector store must be proven, got %s: %s", v.Kind, v.Message)
	}
}
