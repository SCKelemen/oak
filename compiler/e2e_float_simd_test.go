package compiler

// Floating-point vectors, executed (docs/spec/20-types.md section 11.3.7):
// lane-wise arithmetic and fma, the IEEE 754-2019 min/max, lane access, and
// the pairwise reduce_add, checked as bit patterns in the compiled program
// (NEON on AArch64, the portable lane loop elsewhere and under
// -DOAK_PORTABLE_INTRINSICS) and in the interpreter.

import (
	"strings"
	"testing"
)

const floatSimdProgram = `
checks: (): u32 {
  score: u32 = 0
  xs: [4]f32 = [4]f32{1.0, 2.0, 3.0, 4.0}
  ys: [4]f32 = [4]f32{0.5, 0.25, 2.0, -1.0}
  xv: []f32 = view(&xs)
  yv: []f32 = view(&ys)
  a: simd.F32x4 = simd.load_f32x4(xv, 0)
  b: simd.F32x4 = simd.load_f32x4(yv, 0)
  // Lane-wise arithmetic and lane access.
  sum: simd.F32x4 = simd.add_f32x4(a, b)
  score = simd.extract_f32x4(sum, 0) == 1.5 ? score + 1 | score
  score = simd.extract_f32x4(sum, 3) == 3.0 ? score + 1 | score
  prod: simd.F32x4 = simd.mul_f32x4(a, b)
  score = simd.extract_f32x4(prod, 2) == 6.0 ? score + 1 | score
  quot: simd.F32x4 = simd.div_f32x4(a, b)
  score = simd.extract_f32x4(quot, 1) == 8.0 ? score + 1 | score
  // A dot product: fma into a zero accumulator, then the pairwise reduce.
  acc: simd.F32x4 = simd.fma_f32x4(a, b, simd.splat_f32x4(0.0))
  score = simd.reduce_add_f32x4(acc) == 3.0 ? score + 1 | score
  // reduce_add is the pairwise tree (l0 + l1) + (l2 + l3): with 2^24, 1, 1,
  // -2^24 the pairwise grouping gives 1 + (1 - 2^24) + 2^24 ... computed as
  // (2^24 + 1) + (1 - 2^24) = 2^24 + (1 - 2^24) = 1.0 (2^24 + 1 rounds to
  // 2^24), while a left fold would give ((2^24 + 1) + 1) - 2^24 = 0.0.
  big: f32 = 0x1p24
  order: simd.F32x4 = simd.insert_f32x4(simd.insert_f32x4(simd.insert_f32x4(simd.splat_f32x4(1.0), 0, big), 3, -big), 1, 1.0)
  score = simd.reduce_add_f32x4(order) == 1.0 ? score + 1 | score
  // min/max: NaN wins, -0.0 orders below +0.0.
  nan: f32 = f32_bits_u32(u32(2143289344))
  negzero: f32 = f32_bits_u32(u32(2147483648))
  m: simd.F32x4 = simd.min_f32x4(simd.splat_f32x4(negzero), simd.splat_f32x4(0.0))
  score = u32_bits_f32(simd.extract_f32x4(m, 0)) == u32(2147483648) ? score + 1 | score
  n: simd.F32x4 = simd.max_f32x4(simd.splat_f32x4(nan), simd.splat_f32x4(1.0))
  score = is_nan(simd.extract_f32x4(n, 3)) ? score + 1 | score
  // sqrt, neg, abs lane-wise; store back through a span.
  roots: simd.F32x4 = simd.sqrt_f32x4(simd.splat_f32x4(2.0))
  score = u32_bits_f32(simd.extract_f32x4(roots, 2)) == u32(1068827891) ? score + 1 | score
  out: [4]f32
  outs: [*]f32 = span(&out)
  simd.store_f32x4(outs, 0, simd.neg_f32x4(simd.abs_f32x4(b)))
  score = outs[3] == -1.0 ? score + 1 | score
  score = outs[0] == -0.5 ? score + 1 | score
  // f64x2: the same rules at double precision.
  d: simd.F64x2 = simd.insert_f64x2(simd.splat_f64x2(0.1), 1, 0.2)
  s: f64 = simd.reduce_add_f64x2(d)
  score = u64_bits_f64(s) == u64(4599075939470750516) ? score + 1 | score
  w: simd.F64x2 = simd.fma_f64x2(simd.splat_f64x2(0.1), simd.splat_f64x2(10.0), simd.splat_f64x2(-1.0))
  score = simd.extract_f64x2(w, 0) == 5.551115123125783e-17 ? score + 1 | score
  score
}

main: (): i32 {
  i32_bits_u32(checks())
}
`

const floatSimdScore = 13

func TestE2EFloatSimd(t *testing.T) {
	code, abnormal := buildAndRun(t, "floatsimd", floatSimdProgram)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if code != floatSimdScore {
		t.Fatalf("compiled program scored %d of %d checks", code, floatSimdScore)
	}
	// The portable lane loops must agree with the NEON lowering exactly.
	_, code, abnormal = buildAndRunOutput(t, "floatsimdportable", floatSimdProgram, "-DOAK_PORTABLE_INTRINSICS")
	if abnormal || code != floatSimdScore {
		t.Fatalf("portable lowering scored %d of %d checks (abnormal=%v)", code, floatSimdScore, abnormal)
	}
	if got := interpretChecked(t, floatSimdProgram); got != floatSimdScore {
		t.Fatalf("interpreter scored %d of %d checks", got, floatSimdScore)
	}
}

// Lane indices are range-checked: an out-of-range extract traps.
func TestE2EFloatSimdLaneTrap(t *testing.T) {
	_, abnormal := buildAndRun(t, "floatsimdlane", `
main: (): i32 {
  v: simd.F32x4 = simd.splat_f32x4(1.0)
  lane: u32 = 4
  i32_trunc_f32(simd.extract_f32x4(v, lane))
}
`)
	if !abnormal {
		t.Fatalf("out-of-range lane must trap")
	}
}

// The emitted reduce_add is the explicit pairwise tree in both branches.
func TestFloatSimdReduceLowering(t *testing.T) {
	output, err := New().WithSource("reduce.oak", `
total: (v: simd.F32x4): f32 { simd.reduce_add_f32x4(v) }
main: (): i32 { 0 }
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "return (v.lanes[0] + v.lanes[1]) + (v.lanes[2] + v.lanes[3]);") {
		t.Fatalf("reduce_add must lower to the pairwise tree:\n%s", output)
	}
}
