package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Floating point through the native backend (docs/spec/94-assembler.md §9):
// f32/f64 parameters, locals in the callee-saved d8–d15, literals as bit
// patterns, IEEE comparisons, conversions with the C backend's range
// checks, the single-instruction intrinsics, and float spans — every
// value exactly representable so equality holds, the C backend and the
// portable realization as the oracle.
const nativeFloatProgram = `
scale: (x: f32, k: f32) -> f32 = x * k + 1.0

halve: (x: f64) -> f64 = x / 2.0

// A signed-zero-aware comparison chain: NaN compares false, so the
// negation must be spelled at the operand, never inferred.
clamp: (x: f64, lo: f64, hi: f64) -> f64 = x < lo ? lo | (x > hi ? hi | x)

neg_abs: (x: f32) -> f32 = -abs(x)

hypot_sq: (a: f64, b: f64) -> f64 = fma(a, a, b * b)

widen_round: (x: f32) -> f32 = f32_round_f64(f64(x) * 3.0)

to_int: (x: f64) -> i32 = i32_trunc_f64(x)

sat_int: (x: f64) -> u8 = u8_saturating_f64(x)

from_int: (n: i32) -> f64 = f64_round_i32(n)

bits_of: (x: f32) -> u32 = u32_bits_f32(x)

// A float span reduction with a float accumulator in d8 and an integer
// counter in x19.
total: (v: []f32) -> f32 {
  acc: f32 = 0.0
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

fill_f64: (s: [*]f64, x: f64) -> () {
  i: u32 = u32(0)
  while i < len(s) {
    s[i] = x + f64_round_i32(i32_bits_u32(i))
    i = i + u32(1)
  }
}

// Locals across a call: the accumulator survives in a callee-saved register.
combine: (a: f32, b: f32) -> f32 {
  acc: f32 = scale(a, b)
  acc = acc + scale(b, a)
  acc
}

main: (): i32 {
  assert(scale(3.0, 2.0) == 7.0)
  assert(halve(9.0) == 4.5)
  assert(clamp(-1.0, 0.0, 1.0) == 0.0)
  assert(clamp(5.0, 0.0, 1.0) == 1.0)
  assert(clamp(0.5, 0.0, 1.0) == 0.5)
  assert(neg_abs(-2.5) == -2.5)
  assert(hypot_sq(3.0, 4.0) == 25.0)
  assert(widen_round(1.5) == 4.5)
  assert(to_int(-7.9) == i32(-7))
  assert(sat_int(300.0) == u8(255))
  assert(sat_int(-3.0) == u8(0))
  assert(from_int(i32(-12)) == -12.0)
  assert(bits_of(1.0) == u32(1065353216))
  buf: [4]f32
  buf[0] = 1.5
  buf[1] = 2.5
  buf[2] = 3.0
  buf[3] = 35.0
  assert(total(view(&buf)) == 42.0)
  arr: [3]f64
  fill_f64(span(&arr), 0.5)
  assert(arr[2] == 2.5)
  assert(combine(1.0, 2.0) == 6.0)
  42
}
`

// A truncating conversion of an out-of-range value traps in both realizations.
const nativeFloatTrapProgram = `
to_int: (x: f64) -> i32 = i32_trunc_f64(x)

main: (): i32 {
  to_int(3000000000.0)
  0
}
`

func TestE2ENativeFloats(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("floats.oak", nativeFloatProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_floats", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native floats: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"scale", "halve", "clamp", "neg_abs", "hypot_sq", "widen_round", "to_int", "sat_int", "from_int", "bits_of", "total", "fill_f64", "combine"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_floats_c", New().WithSource("floats.oak", nativeFloatProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_floats_portable", New().WithSource("floats.oak", nativeFloatProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	_, _, nativeAbnormal := buildAndRunFrom(t, "native_float_trap", New().WithSource("trap.oak", nativeFloatTrapProgram).WithNativeBodies().WithNativeAsm())
	_, _, cAbnormal := buildAndRunFrom(t, "native_float_trap_c", New().WithSource("trap.oak", nativeFloatTrapProgram))
	if !nativeAbnormal || !cAbnormal {
		t.Fatalf("an out-of-range trunc must trap in both realizations (native abnormal=%v, C abnormal=%v)", nativeAbnormal, cAbnormal)
	}
}
