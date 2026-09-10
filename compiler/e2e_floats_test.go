package compiler

// Floating point, executed (docs/spec/20-types.md section 11.3): the
// compiled program and the interpreter must agree with IEEE 754 bit for bit
// on the correctly rounded operation set. Results are observed as bit
// patterns through the bits conversions and folded into the exit status.

import (
	"strings"
	"testing"
)

const floatProgram = `
Result[T, E]: type = Ok: T | Err: E
Overflow: type = | Overflow

// 0.1 + 0.2 in binary32 is 0x3E99999A (not 0.3's 0x3E99999A? it is: both
// round to the same float; the sum in binary64 does not).
sum_f32: (): u32 {
  a: f32 = 0.1
  b: f32 = 0.2
  u32_bits_f32(a + b)
}

// Two roundings versus one: x * 10.0 - 1.0 rounds the product to exactly
// 1.0 and yields 0.0, while fma(x, 10.0, -1.0) is the exact residual
// +2^-54 (the double nearest 0.1 lies above it). A backend that contracted
// the first form would break the first check; that is what FP_CONTRACT OFF
// and -ffp-contract=off guarantee.
residual: (): u32 {
  x: f64 = 0.1
  score: u32 = 0
  score = x * 10.0 - 1.0 == 0.0 ? score + 1 | score
  score = fma(x, 10.0, -1.0) == 5.551115123125783e-17 ? score + 1 | score
  score
}

checks: (): u32 {
  score: u32 = 0
  // 1.5 as f32 is 0x3FC00000; f32 -> f64 widening is exact (0x3FF8000000000000).
  score = u32_bits_f32(1.5) == u32(1069547520) ? score + 1 | score
  h: f32 = 1.5
  score = u64_bits_f64(f64(h)) == u64(4609434218613702656) ? score + 1 | score
  // Rounding from integers and back: round(2.5) is ties away (3.0),
  // round_even(2.5) is 2.0, trunc(-2.7) is -2.0, floor(-2.5) is -3.0.
  score = round(2.5) == 3.0 ? score + 1 | score
  score = round_even(2.5) == 2.0 ? score + 1 | score
  score = trunc(-2.7) == -2.0 ? score + 1 | score
  score = floor(-2.5) == -3.0 ? score + 1 | score
  score = ceil(-2.5) == -2.0 ? score + 1 | score
  // sqrt is correctly rounded: sqrt(2) as f32 is 0x3FB504F3.
  two: f32 = 2.0
  score = u32_bits_f32(sqrt(two)) == u32(1068827891) ? score + 1 | score
  // NaN compares false on every ordered comparison and on ==; != is true.
  nan: f32 = f32_bits_u32(u32(2143289344))
  score = nan == nan ? score | score + 1
  score = nan < nan ? score | score + 1
  score = nan != nan ? score + 1 | score
  score = is_nan(nan) ? score + 1 | score
  score = is_finite(nan) ? score | score + 1
  // 2019 minimum: NaN wins; -0.0 orders below +0.0. min_num: the number wins.
  score = is_nan(min(nan, 1.0)) ? score + 1 | score
  score = min_num(nan, 1.0) == 1.0 ? score + 1 | score
  negzero: f32 = f32_bits_u32(u32(2147483648))
  score = u32_bits_f32(min(negzero, 0.0)) == u32(2147483648) ? score + 1 | score
  score = negzero == 0.0 ? score + 1 | score
  // Total order: -0.0 < +0.0 < 1.0 < NaN.
  score = total_order(negzero, 0.0) ? score + 1 | score
  score = total_order(1.0, nan) ? score + 1 | score
  score = total_order(nan, 1.0) ? score | score + 1
  // Conversions: saturating clamps, checked reports, trunc truncates.
  big: f32 = 1e10
  score = u8_saturating_f32(big) == u8(255) ? score + 1 | score
  score = i32_saturating_f32(-big) == i32(-2147483648) ? score + 1 | score
  score = u8_saturating_f32(nan) == u8(0) ? score + 1 | score
  score = i32_trunc_f32(-2.7) == i32(-2) ? score + 1 | score
  score = i32_checked_f32(big) ?
    | .Ok(v) => score
    | .Err(e) => score + 1
  score = i32_checked_f32(7.9) ?
    | .Ok(v) => (v == i32(7) ? score + 1 | score)
    | .Err(e) => score
  // round from integers: 16777217 is not representable in f32 and rounds to
  // 16777216; f64 keeps it.
  score = f32_round_i32(i32(16777217)) == 16777216.0 ? score + 1 | score
  score = f64_round_i32(i32(16777217)) == 16777217.0 ? score + 1 | score
  // Division by zero is the IEEE result, never a trap.
  zero: f32 = 0.0
  score = is_infinite(1.0 / zero) ? score + 1 | score
  score = is_nan(zero / zero) ? score + 1 | score
  // copysign and abs are bit operations.
  score = u32_bits_f32(copysign(1.5, negzero)) == u32(3217031168) ? score + 1 | score
  score = abs(-1.5) == 1.5 ? score + 1 | score
  // Grouping is the parse tree (section 11.3.3): addition is not
  // associative, and the left-associative reading is the one that runs.
  // 2^53 + 1.0 rounds back to 2^53 (ties to even), while 1.0 + -2^53 is
  // exact, so the two groupings differ by exactly one.
  large: f64 = 9007199254740992.0
  one: f64 = 1.0
  score = large + one + -large == 0.0 ? score + 1 | score
  score = large + (one + -large) == 1.0 ? score + 1 | score
  score
}

main: (): i32 {
  score: u32 = checks()
  score = sum_f32() == u32(1050253722) ? score + 1 | score
  score = score + residual()
  i32_bits_u32(score)
}
`

// floatProgramScore is the number of checks in floatProgram: 34 in checks,
// one for sum_f32, two in residual.
const floatProgramScore = 37

func TestE2EFloatSemantics(t *testing.T) {
	code, abnormal := buildAndRun(t, "floats", floatProgram)
	if abnormal {
		t.Fatalf("compiled float program trapped")
	}
	if code != floatProgramScore {
		t.Fatalf("compiled program scored %d of %d checks", code, floatProgramScore)
	}
	got := interpretChecked(t, floatProgram)
	if got != floatProgramScore {
		t.Fatalf("interpreter scored %d of %d checks", got, floatProgramScore)
	}
}

// A trapping conversion out of range stops the program (section 11.3.4).
func TestE2EFloatTruncTraps(t *testing.T) {
	_, abnormal := buildAndRun(t, "floattrap", `
main: (): i32 {
  big: f32 = 1e10
  i32_trunc_f32(big)
}
`)
	if !abnormal {
		t.Fatalf("i32_trunc_f32 out of range must trap")
	}
}

// The emitted C: exact hexadecimal literals of the right width, plain
// operators for arithmetic, the contraction pragma, and the math library.
func TestFloatLowering(t *testing.T) {
	output, err := New().WithSource("floats.oak", `
scale: (x: f32, k: f64): f64 {
  y: f32 = x * 1.5
  f64(y) + k * 0.5
}

chain: (a: f32, b: f32, c: f32): f32 {
  a + b + c
}

main: (): i32 { 0 }
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, want := range []string{
		"#pragma STDC FP_CONTRACT OFF",
		"#include <math.h>",
		"#if FLT_EVAL_METHOD != 0",
		"typedef float  f32;",
		"( x * ((f32)0x1.8p+00f) )",
		"( k * ((f64)0x1p-01) )",
		// Grouping is the parse tree: left-associative, every operation
		// parenthesized (docs/spec/20-types.md section 11.3.3).
		"( ( a + b ) + c )",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("emitted C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "oak_mul_f32") || strings.Contains(output, "oak_add_f64") {
		t.Fatalf("float arithmetic must stay a plain C operator, never a wrapping helper:\n%s", output)
	}
}
