package asm

import (
	"strings"
	"testing"
)

// The RV64 vector file under a fixed configuration, verified against the
// Oak body (docs/spec/94-assembler.md §8, §9): the shapes the native
// lowering emits (nativegen/rv64_simd.go), each proven or refused.
func TestRV64VerifyVector(t *testing.T) {
	// A byte span loaded at a guarded index under the slack idiom, compared
	// with zero, the mask read through element 0 at e32 and masked to the
	// sixteen lanes (the tail bits of the mask are unspecified).
	decl := "zero_mask: (b: []u8, i: u32) -> u32"
	oak := "simd.movemask_u8x16(simd.eq_u8x16(simd.load_u8x16(b, i), simd.splat_u8x16(u8(0))))"
	head := `  bind a0, a1 = b
  bind a2 = i
  clobber t0, t1, t2, t3, v0, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 16
  bltu t1, t0, trap
  sub t2, t1, t0
  bltu t2, a2, trap
  add t3, a0, a2
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (t3)
  vmv.v.x v9, zero
  vmseq.vv v0, v8, v9
  li t0, -1
  vmv.v.x v10, t0
  vmerge.vvm v11, v9, v10, v0
  vmslt.vx v0, v11, zero
  vsetivli zero, 1, e32, m1, ta, ma
  vmv.x.s a0, v0
`
	tail := "trap:\n  ebreak"
	if v := rv64Verify(t, decl, oak, head+"  slli a0, a0, 48\n  srli a0, a0, 48\n  ret\n"+tail); v.Kind != VerdictProven {
		t.Fatalf("the zero mask must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Without clearing the tail bits the result depends on them: refused.
	if v := rv64Verify(t, decl, oak, head+"  ret\n"+tail); v.Kind != VerdictMismatch || !strings.Contains(v.Message, "vmask.tail") {
		t.Fatalf("reading the mask's tail bits must be a mismatch naming them, got %s: %s", v.Kind, v.Message)
	}
	// Comparing with one instead of zero is a definite mismatch.
	if v := rv64Verify(t, decl, oak, strings.Replace(head, "  vmv.v.x v9, zero\n  vmseq.vv v0, v8, v9\n", "  li t0, 1\n  vmv.v.x v9, t0\n  vmseq.vv v0, v8, v9\n  vmv.v.x v9, zero\n", 1)+"  slli a0, a0, 48\n  srli a0, a0, 48\n  ret\n"+tail); v.Kind != VerdictMismatch {
		t.Fatalf("comparing with one must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// any/all through vmsne and vcpop over sixteen bytes at the base of a
	// span of proven length.
	anyDecl := "has_seven: (b: []u8) -> Bool"
	anyOak := "simd.any_u8x16(simd.eq_u8x16(simd.load_u8x16(b, u32(0)), simd.splat_u8x16(u8(7))))"
	anyAsm := `  bind a0, a1 = b
  clobber t0, t1, v0, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 16
  bltu t1, t0, trap
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (a0)
  li t0, 7
  vmv.v.x v9, t0
  vmseq.vv v0, v8, v9
  vmv.v.x v10, zero
  li t0, -1
  vmv.v.x v11, t0
  vmerge.vvm v11, v10, v11, v0
  vmsne.vx v0, v11, zero
  vcpop.m a0, v0
  sltu a0, zero, a0
  ret
trap:
  ebreak`
	if v := rv64Verify(t, anyDecl, anyOak, anyAsm); v.Kind != VerdictProven {
		t.Fatalf("any through vcpop must be proven, got %s: %s", v.Kind, v.Message)
	}
	// tbl: the gather under the index-below-sixteen mask is the table
	// lookup; without the mask an index at or past sixteen reads the
	// register's tail.
	tblDecl := "lookup: (tb: []u8, ix: []u8) -> u32"
	tblOak := "simd.movemask_u8x16(simd.tbl_u8x16(simd.load_u8x16(tb, u32(0)), simd.load_u8x16(ix, u32(0))))"
	tblHead := `  bind a0, a1 = tb
  bind a2, a3 = ix
  clobber t0, t1, t2, v0, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  slli t2, a3, 32
  srli t2, t2, 32
  li t0, 16
  bltu t1, t0, trap
  bltu t2, t0, trap
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (a0)
  vle8.v v9, (a2)
`
	tblTail := `  vmslt.vx v0, v10, zero
  vsetivli zero, 1, e32, m1, ta, ma
  vmv.x.s a0, v0
  slli a0, a0, 48
  srli a0, a0, 48
  ret
trap:
  ebreak`
	masked := "  vmsltu.vx v0, v9, t0\n  vrgather.vv v10, v8, v9\n  vmv.v.x v11, zero\n  vmerge.vvm v10, v11, v10, v0\n"
	if v := rv64Verify(t, tblDecl, tblOak, tblHead+masked+tblTail); v.Kind != VerdictProven {
		t.Fatalf("the masked gather must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, tblDecl, tblOak, tblHead+"  vrgather.vv v10, v8, v9\n"+tblTail); v.Kind != VerdictMismatch || !strings.Contains(v.Message, "vgather.tail") {
		t.Fatalf("the unmasked gather must be a mismatch naming the tail, got %s: %s", v.Kind, v.Message)
	}
	// prev by four: slide the previous block down by twelve, the current
	// one up by four over it.
	prevDecl := "shifted: (b: []u8) -> u32"
	prevOak := "simd.movemask_u8x16(simd.prev_u8x16(simd.load_u8x16(b, u32(0)), simd.load_u8x16(b, u32(16)), u32(4)))"
	prevAsm := `  bind a0, a1 = b
  clobber t0, t1, t2, t3, t4, v0, v8, v9, v10
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 16
  bltu t1, t0, trap
  sub t2, t1, t0
  li t4, 16
  bltu t2, t4, trap
  add t3, a0, t4
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (a0)
  vle8.v v9, (t3)
  vslidedown.vi v10, v8, 12
  vslideup.vi v10, v9, 4
  vmslt.vx v0, v10, zero
  vsetivli zero, 1, e32, m1, ta, ma
  vmv.x.s a0, v0
  slli a0, a0, 48
  srli a0, a0, 48
  ret
trap:
  ebreak`
	if v := rv64Verify(t, prevDecl, prevOak, prevAsm); v.Kind != VerdictProven {
		t.Fatalf("prev through the slides must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A vector spilled to the frame and reloaded whole.
	spillDecl := "spilled: (b: []u8) -> u32"
	spillOak := "simd.movemask_u8x16(simd.load_u8x16(b, u32(0)))"
	spillAsm := `  bind a0, a1 = b
  clobber t0, t1, t6, v0, v8, v9
  frame 16
  slli t1, a1, 32
  srli t1, t1, 32
  li t0, 16
  bltu t1, t0, trap
  addi sp, sp, -16
  vsetivli zero, 16, e8, m1, ta, ma
  vle8.v v8, (a0)
  addi t6, sp, 0
  vse8.v v8, (t6)
  vle8.v v9, (t6)
  vmslt.vx v0, v9, zero
  vsetivli zero, 1, e32, m1, ta, ma
  vmv.x.s a0, v0
  slli a0, a0, 48
  srli a0, a0, 48
  addi sp, sp, 16
  ret
trap:
  ebreak`
	if v := rv64Verify(t, spillDecl, spillOak, spillAsm); v.Kind != VerdictProven {
		t.Fatalf("a spilled and reloaded vector must be proven, got %s: %s", v.Kind, v.Message)
	}
	// The ordered float dot product over two f32 spans: the sequential
	// fold from zero, as vfredosum computes it; the reduction's tail is
	// unspecified and vfmv.f.s reads element 0 only.
	dotDecl := "dot4: (a: []f32, b: []f32) -> f32"
	dotOak := "(((0.0 + a[0] * b[0]) + a[1] * b[1]) + a[2] * b[2]) + a[3] * b[3]"
	dotAsm := `  bind a0, a1 = a
  bind a2, a3 = b
  clobber t0, t1, t2, ft0, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  slli t2, a3, 32
  srli t2, t2, 32
  li t0, 4
  bltu t1, t0, trap
  bltu t2, t0, trap
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v8, (a0)
  vle32.v v9, (a2)
  vfmul.vv v8, v8, v9
  fmv.w.x ft0, zero
  vfmv.v.f v10, ft0
  vfredosum.vs v11, v8, v10
  vfmv.f.s fa0, v11
  ret
trap:
  ebreak`
	if v := rv64Verify(t, dotDecl, dotOak, dotAsm); v.Kind != VerdictProven {
		t.Fatalf("the ordered dot product must be proven, got %s: %s", v.Kind, v.Message)
	}
	// The pairwise grouping is another sum: a mismatch.
	pairwise := "((0.0 + a[0] * b[0]) + a[1] * b[1]) + (a[2] * b[2] + a[3] * b[3])"
	if v := rv64Verify(t, dotDecl, pairwise, dotAsm); v.Kind != VerdictMismatch {
		t.Fatalf("the pairwise grouping against the ordered reduction must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// A register AVL keeps the unit trusted.
	if v := rv64Verify(t, anyDecl, anyOak, strings.Replace(anyAsm, "  vsetivli zero, 16, e8, m1, ta, ma\n", "  vsetvli zero, t1, e8, m1, ta, ma\n", 1)); v.Kind != VerdictTrusted || !strings.Contains(v.Message, "register AVL") {
		t.Fatalf("a register AVL must leave the unit trusted, got %s: %s", v.Kind, v.Message)
	}
}

// The float vector forms the RV64 native lowering emits (nativegen/rv64_simd.go,
// the eleventh increment) decide against the Oak simd operations: the
// min/max sequence with the NaN propagation restored through masks, the
// insert through vid/vmseq/vfmerge, the extract through a slide, the sign
// injections, and the pairwise reduce through slides.
func TestRV64VerifyFloatVector(t *testing.T) {
	// Two f32 spans of proven length, lanes loaded at their bases.
	head := `  bind a0, a1 = a
  bind a2, a3 = b
  clobber t0, t1, t2, t6, ft0, ft1, v0, v1, v8, v9, v10, v11
  slli t1, a1, 32
  srli t1, t1, 32
  slli t2, a3, 32
  srli t2, t2, 32
  li t0, 4
  bltu t1, t0, trap
  bltu t2, t0, trap
  vsetivli zero, 4, e32, m1, ta, ma
  vle32.v v8, (a0)
  vle32.v v9, (a2)
`
	tail := "trap:\n  ebreak"
	// min: vfmin then the NaN operands merged back over the result; the
	// result is read through the pairwise reduce's first lane pair.
	lane0 := "  vfmv.f.s fa0, v10\n  ret\n"
	decl := "least: (a: []f32, b: []f32) -> f32"
	minSeq := "  vfmin.vv v10, v8, v9\n  vmfne.vv v0, v8, v8\n  vmerge.vvm v10, v10, v8, v0\n  vmfne.vv v0, v9, v9\n  vmerge.vvm v10, v10, v9, v0\n"
	if v := rv64Verify(t, decl, "simd.extract_f32x4(simd.min_f32x4(simd.load_f32x4(a, u32(0)), simd.load_f32x4(b, u32(0))), 0)", head+minSeq+lane0+tail); v.Kind != VerdictProven {
		t.Fatalf("min through vfmin and the NaN merges must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Without the merges vfmin suppresses a NaN operand: a mismatch.
	if v := rv64Verify(t, decl, "simd.extract_f32x4(simd.min_f32x4(simd.load_f32x4(a, u32(0)), simd.load_f32x4(b, u32(0))), 0)", head+"  vfmin.vv v10, v8, v9\n"+lane0+tail); v.Kind != VerdictMismatch {
		t.Fatalf("bare vfmin against min must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// div, sqrt, neg, abs lane-wise; extract of lane 2 through a slide.
	body := "simd.extract_f32x4(simd.neg_f32x4(simd.abs_f32x4(simd.sqrt_f32x4(simd.div_f32x4(simd.load_f32x4(a, u32(0)), simd.load_f32x4(b, u32(0)))))), 2)"
	seq := "  vfdiv.vv v10, v8, v9\n  vfsqrt.v v10, v10\n  vfsgnjx.vv v10, v10, v10\n  vfsgnjn.vv v10, v10, v10\n  vslidedown.vi v11, v10, 2\n  vfmv.f.s fa0, v11\n  ret\n"
	if v := rv64Verify(t, "third: (a: []f32, b: []f32) -> f32", body, head+seq+tail); v.Kind != VerdictProven {
		t.Fatalf("div/sqrt/abs/neg and a slid extract must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "third: (a: []f32, b: []f32) -> f32", body, head+strings.Replace(seq, "vslidedown.vi v11, v10, 2", "vslidedown.vi v11, v10, 1", 1)+tail); v.Kind != VerdictMismatch {
		t.Fatalf("extracting the wrong lane must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// insert at lane 1 through vid/vmseq/vfmerge, read back at lane 1.
	insert := "  fmv.w.x ft0, zero\n  vid.v v11\n  li t6, 1\n  vmseq.vx v0, v11, t6\n  vfmerge.vfm v8, v8, ft0, v0\n  vslidedown.vi v11, v8, 1\n  vfmv.f.s fa0, v11\n  ret\n"
	if v := rv64Verify(t, "set1: (a: []f32, b: []f32) -> f32", "simd.extract_f32x4(simd.insert_f32x4(simd.load_f32x4(a, u32(0)), 1, 0.0), 1)", head+insert+tail); v.Kind != VerdictProven {
		t.Fatalf("insert through vid/vmseq/vfmerge must be proven, got %s: %s", v.Kind, v.Message)
	}
	// reduce_add as the pairwise tree through two slide-and-add steps.
	reduce := "  vfmul.vv v10, v8, v9\n  vslidedown.vi v11, v10, 1\n  vfadd.vv v10, v10, v11\n  vslidedown.vi v11, v10, 2\n  vfadd.vv v10, v10, v11\n  vfmv.f.s fa0, v10\n  ret\n"
	if v := rv64Verify(t, "dot: (a: []f32, b: []f32) -> f32", "simd.reduce_add_f32x4(simd.mul_f32x4(simd.load_f32x4(a, u32(0)), simd.load_f32x4(b, u32(0))))", head+reduce+tail); v.Kind != VerdictProven {
		t.Fatalf("the pairwise reduce through slides must be proven, got %s: %s", v.Kind, v.Message)
	}
	// vfredosum's sequential fold is the other grouping: a mismatch.
	ordered := "  vfmul.vv v10, v8, v9\n  fmv.w.x ft0, zero\n  vfmv.v.f v11, ft0\n  vfredosum.vs v10, v10, v11\n  vfmv.f.s fa0, v10\n  ret\n"
	if v := rv64Verify(t, "dot: (a: []f32, b: []f32) -> f32", "simd.reduce_add_f32x4(simd.mul_f32x4(simd.load_f32x4(a, u32(0)), simd.load_f32x4(b, u32(0))))", head+ordered+tail); v.Kind != VerdictMismatch {
		t.Fatalf("the ordered reduction against the pairwise tree must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
