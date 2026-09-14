package asm

import (
	"strings"
	"testing"
)

// Floating point as uninterpreted operations (docs/spec/94-assembler.md
// §8): a unit is proven equal to its Oak body up to the IEEE operations —
// the same operations over the same operands in the same order — and a
// unit that contracts, reorders, or substitutes an operation is refused.
func TestVerifyFloatScalar(t *testing.T) {
	decl := "axpy: (a, x, y: f64) -> f64"
	bind := "  bind d0 = a\n  bind d1 = x\n  bind d2 = y\n"
	// fma is fmadd: one rounding on both sides.
	fused := verifyCase(t, decl, "fma(a, x, y)", bind+"  fmadd d0, d0, d1, d2\n  ret")
	if fused.Kind != VerdictProven {
		t.Fatalf("fma against fmadd must be proven, got %s: %s", fused.Kind, fused.Message)
	}
	// a*x + y is two roundings: fmadd contracts them, a mismatch.
	contracted := verifyCase(t, decl, "a * x + y", bind+"  fmadd d0, d0, d1, d2\n  ret")
	if contracted.Kind != VerdictMismatch {
		t.Fatalf("contracting a*x + y into fmadd must be a mismatch, got %s: %s", contracted.Kind, contracted.Message)
	}
	// The two-instruction form is the body.
	separate := verifyCase(t, decl, "a * x + y", bind+"  fmul d0, d0, d1\n  fadd d0, d0, d2\n  ret")
	if separate.Kind != VerdictProven {
		t.Fatalf("fmul then fadd must be proven, got %s: %s", separate.Kind, separate.Message)
	}
	// Reordering the operands of a non-commutative operation is caught;
	// commutativity is not assumed either (x*a is another application).
	swapped := verifyCase(t, decl, "a - x", "  bind d0 = a\n  bind d1 = x\n  bind d2 = y\n  fsub d0, d1, d0\n  ret")
	if swapped.Kind != VerdictMismatch {
		t.Fatalf("a - x against x - a must be a mismatch, got %s: %s", swapped.Kind, swapped.Message)
	}
	// Negation, absolute value, and sqrt; a comparison through fcmp and
	// fcsel; min through fmin.
	if v := verifyCase(t, "root: (x: f64) -> f64", "sqrt(abs(-x))", "  bind d0 = x\n  fneg d0, d0\n  fabs d0, d0\n  fsqrt d0, d0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("sqrt(abs(-x)) must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "lesser: (a, b: f64) -> f64", "a < b ? a | b", "  bind d0 = a\n  bind d1 = b\n  fcmp d0, d1\n  fcsel d0, d0, d1, mi\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("a < b ? a | b through fcmp/fcsel must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "lesser: (a, b: f64) -> f64", "a < b ? a | b", "  bind d0 = a\n  bind d1 = b\n  fcmp d0, d1\n  fcsel d0, d0, d1, le\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("selecting on le for < must be a mismatch (NaN and equal operands), got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "least: (a, b: f32) -> f32", "min(a, b)", "  bind s0 = a\n  bind s1 = b\n  fmin s0, s0, s1\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("min against fmin must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "least: (a, b: f32) -> f32", "min(a, b)", "  bind s0 = a\n  bind s1 = b\n  fminnm s0, s0, s1\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("min against fminnm (NaN suppressed) must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Conversions: an integer to a float and back, and a width change.
	if v := verifyCase(t, "to_f32: (n: u32) -> f32", "f32(n)", "  bind w0 = n\n  ucvtf s0, w0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f32(n) against ucvtf must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "to_f32: (n: u32) -> f32", "f32(n)", "  bind w0 = n\n  scvtf s0, w0\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("f32(n) against scvtf must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "widen: (x: f32) -> f64", "f64(x)", "  bind s0 = x\n  fcvt d0, s0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64(x) against fcvt must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "floor_u: (x: f64) -> u64", "u64(x)", "  bind d0 = x\n  fcvtzu x0, d0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("u64(x) against fcvtzu must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A constant folds: the literal's bits.
	if v := verifyCase(t, "twice: (x: f64) -> f64", "x * 2.0", "  bind d0 = x\n  clobber v1\n  fmov d1, #2.0\n  fmul d0, d0, d1\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("x * 2.0 against fmov/fmul must be proven, got %s: %s", v.Kind, v.Message)
	}
	// The bits forms are bit moves, not conversions.
	if v := verifyCase(t, "bits: (x: f32) -> u32", "u32_bits_f32(x)", "  bind s0 = x\n  fmov w0, s0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("u32_bits_f32 against fmov must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "from_bits: (n: u64) -> f64", "f64_bits_u64(n)", "  bind x0 = n\n  fmov d0, x0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64_bits_u64 against fmov must be proven, got %s: %s", v.Kind, v.Message)
	}
	if !strings.Contains(fused.Message, "proven") {
		t.Fatalf("unexpected message %q", fused.Message)
	}
}

// Float vectors: the lane operations, fma through fmla, the pairwise
// reduce_add tree through faddp, lane access, and the mismatches — a
// left-fold reduction, the number-preferring minimum for min.
func TestVerifyFloatVector(t *testing.T) {
	dot := "dot: (a, b: simd.F32x4) -> f32"
	body := "simd.reduce_add_f32x4(simd.mul_f32x4(a, b))"
	tree := verifyCase(t, dot, body, "  bind v0 = a\n  bind v1 = b\n  fmul v0.4s, v0.4s, v1.4s\n  faddp v0.4s, v0.4s, v0.4s\n  faddp s0, v0.2s\n  ret")
	if tree.Kind != VerdictProven {
		t.Fatalf("the pairwise dot product must be proven, got %s: %s", tree.Kind, tree.Message)
	}
	fold := verifyCase(t, dot, body, "  bind v0 = a\n  bind v1 = b\n  clobber v2, v3\n  fmul v0.4s, v0.4s, v1.4s\n  mov s2, v0.s[0]\n  mov s3, v0.s[1]\n  fadd s2, s2, s3\n  mov s3, v0.s[2]\n  fadd s2, s2, s3\n  mov s3, v0.s[3]\n  fadd s0, s2, s3\n  ret")
	if fold.Kind != VerdictMismatch {
		t.Fatalf("a left-fold reduction must be a mismatch (the pairwise grouping is the semantics), got %s: %s", fold.Kind, fold.Message)
	}
	fma := "madd: (a, b, c: simd.F32x4) -> simd.F32x4"
	if v := verifyCase(t, fma, "simd.fma_f32x4(a, b, c)", "  bind v0 = a\n  bind v1 = b\n  bind v2 = c\n  fmla v2.4s, v0.4s, v1.4s\n  mov v0.16b, v2.16b\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("fma against fmla must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, fma, "simd.add_f32x4(simd.mul_f32x4(a, b), c)", "  bind v0 = a\n  bind v1 = b\n  bind v2 = c\n  fmla v2.4s, v0.4s, v1.4s\n  mov v0.16b, v2.16b\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("contracting a lane-wise multiply and add into fmla must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	pair := "pair: (a, b: simd.F64x2) -> simd.F64x2"
	if v := verifyCase(t, pair, "simd.add_f64x2(a, b)", "  bind v0 = a\n  bind v1 = b\n  fadd v0.2d, v0.2d, v1.2d\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64x2 add must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, pair, "simd.min_f64x2(a, b)", "  bind v0 = a\n  bind v1 = b\n  fmin v0.2d, v0.2d, v1.2d\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64x2 min against fmin must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, pair, "simd.min_f64x2(a, b)", "  bind v0 = a\n  bind v1 = b\n  fminnm v0.2d, v0.2d, v1.2d\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("f64x2 min against fminnm must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, pair, "simd.neg_f64x2(simd.abs_f64x2(simd.sqrt_f64x2(a)))", "  bind v0 = a\n  bind v1 = b\n  fsqrt v0.2d, v0.2d\n  fabs v0.2d, v0.2d\n  fneg v0.2d, v0.2d\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("lane-wise sqrt/abs/neg must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "third: (a: simd.F32x4) -> f32", "simd.extract_f32x4(a, 2)", "  bind v0 = a\n  mov s0, v0.s[2]\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("extract against a lane move must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "third: (a: simd.F32x4) -> f32", "simd.extract_f32x4(a, 2)", "  bind v0 = a\n  mov s0, v0.s[1]\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("extracting the wrong lane must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "set1: (a: simd.F32x4, x: f32) -> simd.F32x4", "simd.insert_f32x4(a, 1, x)", "  bind v0 = a\n  bind s1 = x\n  mov v0.s[1], v1.s[0]\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("insert against a lane insert must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "fill: (x: f32) -> simd.F32x4", "simd.splat_f32x4(x)", "  bind s0 = x\n  dup v0.4s, v0.s[0]\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("splat against dup must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A splat of a float literal is the literal at the lane's format (the
	// native backend's `fmov` then `dup`), not its 64-bit pattern.
	if v := verifyCase(t, "twice: (v: simd.F32x4) -> simd.F32x4", "simd.mul_f32x4(v, simd.splat_f32x4(2.0))", "  bind v0 = v\n  clobber v1\n  fmov s1, #2.0\n  dup v1.4s, v1.s[0]\n  fmul v0.4s, v0.4s, v1.4s\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("a splat literal must be proven at the lane width, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "double: (v: simd.F64x2) -> simd.F64x2", "simd.mul_f64x2(v, simd.splat_f64x2(2.0))", "  bind v0 = v\n  clobber v1\n  fmov d1, #2.0\n  dup v1.2d, v1.d[0]\n  fmul v0.2d, v0.2d, v1.2d\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("an f64 splat literal must be proven, got %s: %s", v.Kind, v.Message)
	}
}
