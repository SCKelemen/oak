package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Floating-point vectors through the native backend (docs/spec/93-simd.md
// section 1.2a and section 1.4, nativegen/simd.go): every lowered
// operation over known values, each function's result a number the C
// backend must reproduce bit for bit — the pairwise reduce_add grouping,
// the one-rounding fma, the IEEE 754-2019 min/max on NaN and the signed
// zeros, and lane access — with the vectors loaded through f32 views (a
// q load over lanes wider than a byte goes through the element address
// the checker proves inside the span).
const nativeFloatSimdProgram = `
// Lane-wise arithmetic through views: 1 + 2 + 4 + 8 + 16.
arith: (xs: []f32, ys: []f32) -> u32 {
  a: simd.F32x4 = simd.load_f32x4(xs, u32(0))
  b: simd.F32x4 = simd.load_f32x4(ys, u32(0))
  sum: simd.F32x4 = simd.add_f32x4(a, b)
  prod: simd.F32x4 = simd.mul_f32x4(a, b)
  quot: simd.F32x4 = simd.div_f32x4(a, b)
  diff: simd.F32x4 = simd.sub_f32x4(a, b)
  s0: u32 = simd.extract_f32x4(sum, u32(0)) == 1.5 ? u32(1) | u32(0)
  s3: u32 = simd.extract_f32x4(sum, u32(3)) == 3.0 ? u32(2) | u32(0)
  p2: u32 = simd.extract_f32x4(prod, u32(2)) == 6.0 ? u32(4) | u32(0)
  q1: u32 = simd.extract_f32x4(quot, u32(1)) == 8.0 ? u32(8) | u32(0)
  d0: u32 = simd.extract_f32x4(diff, u32(0)) == 0.5 ? u32(16) | u32(0)
  s0 + s3 + p2 + q1 + d0
}

// A dot product: fma into a zero accumulator, then the pairwise reduce.
dot: (xs: []f32, ys: []f32) -> f32 {
  a: simd.F32x4 = simd.load_f32x4(xs, u32(0))
  b: simd.F32x4 = simd.load_f32x4(ys, u32(0))
  simd.reduce_add_f32x4(simd.fma_f32x4(a, b, simd.splat_f32x4(0.0)))
}

// reduce_add is the pairwise tree (l0 + l1) + (l2 + l3): with 2^24, 1, 1,
// -2^24 it yields 1.0, where a left fold would yield 0.0.
pairwise: () -> u32 {
  big: f32 = 16777216.0
  order: simd.F32x4 = simd.insert_f32x4(simd.insert_f32x4(simd.insert_f32x4(simd.splat_f32x4(1.0), u32(0), big), u32(3), -big), u32(1), 1.0)
  simd.reduce_add_f32x4(order) == 1.0 ? u32(1) | u32(0)
}

// min/max: -0.0 orders below +0.0, and a NaN operand yields NaN.
minmax: () -> u32 {
  negzero: f32 = f32_bits_u32(u32(2147483648))
  nan: f32 = f32_bits_u32(u32(2143289344))
  m: simd.F32x4 = simd.min_f32x4(simd.splat_f32x4(negzero), simd.splat_f32x4(0.0))
  x: simd.F32x4 = simd.max_f32x4(simd.splat_f32x4(nan), simd.splat_f32x4(1.0))
  lo: u32 = u32_bits_f32(simd.extract_f32x4(m, u32(0))) == u32(2147483648) ? u32(1) | u32(0)
  top: f32 = simd.extract_f32x4(x, u32(3))
  hi: u32 = top != top ? u32(2) | u32(0)
  lo + hi
}

// sqrt lane-wise; neg and abs stored back through a span.
unary: (ys: []f32, out: [*]f32) -> u32 {
  b: simd.F32x4 = simd.load_f32x4(ys, u32(0))
  roots: simd.F32x4 = simd.sqrt_f32x4(simd.splat_f32x4(2.0))
  simd.store_f32x4(out, u32(0), simd.neg_f32x4(simd.abs_f32x4(b)))
  u32_bits_f32(simd.extract_f32x4(roots, u32(2))) == u32(1068827891) ? u32(1) | u32(0)
}

// f64x2: the same rules at double precision.
doubles: () -> u32 {
  d: simd.F64x2 = simd.insert_f64x2(simd.splat_f64x2(0.1), u32(1), 0.2)
  s: f64 = simd.reduce_add_f64x2(d)
  w: simd.F64x2 = simd.fma_f64x2(simd.splat_f64x2(0.1), simd.splat_f64x2(10.0), simd.splat_f64x2(-1.0))
  a: u32 = u64_bits_f64(s) == u64(4599075939470750516) ? u32(1) | u32(0)
  b: u32 = simd.extract_f64x2(w, u32(0)) == 5.551115123125783e-17 ? u32(2) | u32(0)
  a + b
}

// A float vector across a native-to-native call: scale keeps the vector
// register contract at its native entry.
scale: (v: simd.F32x4) -> simd.F32x4 = simd.mul_f32x4(v, simd.splat_f32x4(2.0))

scaled: (xs: []f32) -> f32 = simd.reduce_add_f32x4(scale(simd.load_f32x4(xs, u32(0))))

// u32 lanes loaded through a view (the element-address load): 7 sits in
// lane 1.
words_view: (w: []u32) -> u32 {
  v: simd.U32x4 = simd.load_u32x4(w, u32(0))
  simd.any_u32x4(simd.eq_u32x4(v, simd.splat_u32x4(u32(7)))) ? u32(1) | u32(0)
}

main: (): u32 {
  xs: [4]f32 = [4]f32{1.0, 2.0, 3.0, 4.0}
  ys: [4]f32 = [4]f32{0.5, 0.25, 2.0, -1.0}
  ws: [4]u32 = [4]u32{u32(1), u32(7), u32(3), u32(9)}
  out: [4]f32
  ok1: Bool = arith(view(&xs), view(&ys)) == u32(31)
  ok2: Bool = dot(view(&xs), view(&ys)) == 3.0
  ok3: Bool = pairwise() == u32(1)
  ok4: Bool = minmax() == u32(3)
  ok5: Bool = unary(view(&ys), span(&out)) == u32(1)
  ok6: Bool = out[3] == -1.0 && out[0] == -0.5
  ok7: Bool = doubles() == u32(3)
  ok8: Bool = scaled(view(&xs)) == 20.0
  ok9: Bool = words_view(view(&ws)) == u32(1)
  ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 ? u32(42) | (ok1 ? u32(0) | u32(1)) + (ok2 ? u32(0) | u32(2)) + (ok3 ? u32(0) | u32(4)) + (ok4 ? u32(0) | u32(8)) + (ok5 ? u32(0) | u32(16)) + (ok6 ? u32(0) | u32(32)) + (ok7 ? u32(0) | u32(64)) + (ok8 ? u32(0) | u32(128)) + (ok9 ? u32(0) | u32(200))
}
`

func TestE2ENativeFloatSimd(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("native_float_simd.oak", nativeFloatSimdProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_float_simd", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native float simd: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	// scale carries a vector in its signature, so its native entry is the
	// suffixed symbol (nativegen.VectorContractSuffix).
	for _, fn := range []string{"arith", "dot", "pairwise", "minmax", "unary", "doubles", "scale_neon_abi", "scaled", "words_view"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The verifier decides the float units up to the IEEE operations
	// (docs/spec/94-assembler.md §8, eighth increment): each is proven
	// equal to its Oak body, the vector-signature entry on both halves.
	for _, fn := range []string{"arith", "dot", "pairwise", "minmax", "unary", "doubles", "scale_neon_abi", "scaled", "words_view"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	// The C backend (NEON intrinsics) agrees bit for bit.
	if _, code, abnormal := buildAndRunFrom(t, "native_float_simd_c", New().WithSource("native_float_simd.oak", nativeFloatSimdProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	// And so do the portable lane loops.
	if _, code, abnormal := buildAndRunFrom(t, "native_float_simd_portable", New().WithSource("native_float_simd.oak", nativeFloatSimdProgram), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable lowering: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
