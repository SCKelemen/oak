package compiler

import (
	"strings"
	"testing"
)

// Floating-point vectors through the RV64 native lane (docs/spec/93-simd.md
// section 1.2a and section 1.4, nativegen/rv64_simd.go): the float corpus of
// e2e_native_float_simd_test.go without the function whose signature
// carries a vector (the LP64 lane-array contract stays with the C backend),
// lowered to RVV under `vsetivli` configurations on a hard-float processor
// with V, and executed under QEMU at two vector lengths beside the C
// backend's realization — the pairwise reduce_add grouping, the
// one-rounding fma, the IEEE 754-2019 min/max on NaN and the signed zeros,
// lane access, and the f64 lanes.
const nativeRV64FloatSimdProgram = `
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

// u32 lanes loaded through a view: 7 sits in lane 1.
words_view: (w: []u32) -> u32 {
  v: simd.U32x4 = simd.load_u32x4(w, u32(0))
  simd.any_u32x4(simd.eq_u32x4(v, simd.splat_u32x4(u32(7)))) ? u32(1) | u32(0)
}

// A float vector across a native-to-native call: scale keeps the vector
// register contract at its native entry (v8 in, v8 out under the RVV psABI).
scale: (v: simd.F32x4) -> simd.F32x4 = simd.mul_f32x4(v, simd.splat_f32x4(2.0))

scaled: (xs: []f32) -> f32 = simd.reduce_add_f32x4(scale(simd.load_f32x4(xs, u32(0))))

// The same through the C boundary: a foreign pointer local keeps this
// caller on the C backend, which reaches scale through the converting shim.
c_scaled: (xs: []f32) -> f32 {
  nothing: c.Ptr = c.null()
  _ = nothing
  simd.reduce_add_f32x4(scale(simd.load_f32x4(xs, u32(0))))
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
  ok8: Bool = words_view(view(&ws)) == u32(1)
  ok9: Bool = scaled(view(&xs)) == 20.0
  ok10: Bool = c_scaled(view(&xs)) == 20.0
  ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 && ok10 ? u32(42) | (ok1 ? u32(0) | u32(1)) + (ok2 ? u32(0) | u32(2)) + (ok3 ? u32(0) | u32(4)) + (ok4 ? u32(0) | u32(8)) + (ok5 ? u32(0) | u32(16)) + (ok6 ? u32(0) | u32(32)) + (ok7 ? u32(0) | u32(64)) + (ok8 ? u32(0) | u32(128)) + (ok9 ? u32(0) | u32(200)) + (ok10 ? u32(0) | u32(210))
}
`

// The functions the rv64 lane lowers (main addresses owned arrays and stays
// with the C backend on both lanes).
var nativeRV64FloatSimdFunctions = []string{"arith", "dot", "pairwise", "minmax", "unary", "doubles", "words_view", "scale_rvv_abi", "scaled"}

// rv64LinuxVector is the hard-float processor with V the float vectors need.
const rv64LinuxVectorCPU = "generic_rv64+m+a+f+d+v"

func TestE2ENativeRV64FloatSimdLowers(t *testing.T) {
	_, infos := nativeRV64LowerCPU(t, rv64Linux, rv64LinuxVectorCPU, nativeRV64FloatSimdProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range nativeRV64FloatSimdFunctions {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	// The float vector-signature entry and its caller are proven by the
	// verifier under the v8 contract (docs/spec/94-assembler.md §9).
	for _, fn := range []string{"scale_rvv_abi", "scaled"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	// The C emitter's shim over the float entry, called from the C side.
	native, _ := nativeRV64LowerCPU(t, rv64Linux, rv64LinuxVectorCPU, nativeRV64FloatSimdProgram)
	for _, text := range []string{"vfloat32m1_t", "scale_rvv_abi", "__riscv_vle32_v_f32m1", "__riscv_vse32_v_f32m1"} {
		if !strings.Contains(native.C, text) {
			t.Errorf("the emitted C lacks %q (the RVV shim)", text)
		}
	}
	// Without V the float vector bodies stay with the C backend.
	_, infos = nativeRV64Lower(t, rv64Linux, nativeRV64FloatSimdProgram)
	if joined := strings.Join(infos, "\n"); !strings.Contains(joined, "arith left to the C backend (the fixed simd vectors need the vector extension") {
		t.Fatalf("a processor without V must leave the float vector bodies to the C backend:\n%s", joined)
	}
}

// Under QEMU with V at two vector lengths, beside the C backend alone.
func TestE2ENativeRV64FloatSimdUnderQEMU(t *testing.T) {
	skipInShort(t)
	native, infos := nativeRV64LowerCPU(t, rv64Linux, rv64LinuxVectorCPU, nativeRV64FloatSimdProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range nativeRV64FloatSimdFunctions {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Fatalf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	for _, vlen := range []int{128, 256} {
		if out := runNativeRV64BareWith(t, "native_rv64_float_simd", native, nativeRV64Run{hardFloat: true, vector: true, vlen: vlen}); !strings.Contains(out, "0000002a\n") {
			t.Fatalf("native float vectors under QEMU (VLEN %d) did not exit 42:\n%s", vlen, out)
		}
	}
	cOnly, err := New().WithSource("native.oak", nativeRV64FloatSimdProgram).WithTarget(rv64Linux).WithCPU(rv64LinuxVectorCPU).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if out := runNativeRV64BareWith(t, "native_rv64_float_simd_c", NativeOutput{C: cOnly}, nativeRV64Run{hardFloat: true, vector: true, vlen: 128}); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("C backend under QEMU did not exit 42:\n%s", out)
	}
}
