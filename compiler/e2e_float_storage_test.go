package compiler

// Storage formats, hexadecimal literals, and the c.Float rows, executed
// (docs/spec/20-types.md sections 11.3.1, 11.3.2; 92-ffi.md section 2.2):
// binary16 and bfloat16 bit patterns are checked against the IEEE values,
// in the compiled program and in the interpreter.

import "testing"

const floatStorageProgram = `
sqrtf: (x: c.Float): c.Float = c.extern("sqrtf")

checks: (): u32 {
  score: u32 = 0
  // binary16 patterns: 1.0 = 0x3C00, -2.0 = 0xC000, 65504 (max) = 0x7BFF,
  // 65520 rounds to infinity (0x7C00), 2^-24 (smallest subnormal) = 0x0001,
  // 2^-25 ties to even (0), 1.5 * 2^-25 rounds up to 0x0001.
  score = u16_bits_f16(f16_round_f32(1.0)) == u16(15360) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(-2.0)) == u16(49152) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(65504.0)) == u16(31743) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(65520.0)) == u16(31744) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(0x1p-24)) == u16(1) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(0x1p-25)) == u16(0) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(0x1.8p-25)) == u16(1) ? score + 1 | score
  // Ties to even in the normal range: 1 + 2^-11 is halfway between 1.0 and
  // the next half (1 + 2^-10); it rounds to the even 0x3C00. 1 + 3*2^-12
  // is above halfway and rounds up to 0x3C01.
  score = u16_bits_f16(f16_round_f32(0x1.002p0)) == u16(15360) ? score + 1 | score
  score = u16_bits_f16(f16_round_f32(0x1.003p0)) == u16(15361) ? score + 1 | score
  // Widening is exact: 0x3C01 is 1 + 2^-10.
  score = f32(f16_bits_u16(u16(15361))) == 0x1.004p0 ? score + 1 | score
  h: f16 = f16_bits_u16(u16(1))
  score = f32(h) == 0x1p-24 ? score + 1 | score
  // NaN stays NaN and quiet; infinity widens to infinity.
  nan: f32 = f32_bits_u32(u32(2143289344))
  score = is_nan(f32(f16_round_f32(nan))) ? score + 1 | score
  inf: f32 = f32_bits_u32(u32(2139095040))
  score = is_infinite(f32(f16_round_f32(inf))) ? score + 1 | score
  // bfloat16: 1.0 = 0x3F80; 1 + 2^-8 is a tie and rounds to even 0x3F80;
  // 1 + 3*2^-9 rounds up to 0x3F81; the widening is the upper half.
  score = u16_bits_bf16(bf16_round_f32(1.0)) == u16(16256) ? score + 1 | score
  score = u16_bits_bf16(bf16_round_f32(0x1.01p0)) == u16(16256) ? score + 1 | score
  score = u16_bits_bf16(bf16_round_f32(0x1.018p0)) == u16(16257) ? score + 1 | score
  b: bf16 = bf16_bits_u16(u16(16257))
  score = f32(b) == 0x1.02p0 ? score + 1 | score
  // Hexadecimal literals are exact: 0x1.8p1 is 3.0, 0x1p-126 is the
  // smallest f32 normal (bits 0x00800000).
  score = 0x1.8p1 == 3.0 ? score + 1 | score
  small: f32 = 0x1p-126
  score = u32_bits_f32(small) == u32(8388608) ? score + 1 | score
  // c.Float crosses the boundary bit-preservingly: libm's sqrtf agrees with
  // the intrinsic on 2.0 (both correctly rounded).
  two: f32 = 2.0
  score = f32(sqrtf(c.Float(two))) == sqrt(two) ? score + 1 | score
  score
}

main: (): i32 {
  i32_bits_u32(checks())
}
`

const floatStorageScore = 20

func TestE2EFloatStorageFormats(t *testing.T) {
	code, abnormal := buildAndRun(t, "floatstorage", floatStorageProgram)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if code != floatStorageScore {
		t.Fatalf("compiled program scored %d of %d checks", code, floatStorageScore)
	}
}

// The interpreter agrees on everything but the extern call, which it cannot
// make; the program is re-run without that check.
func TestInterpreterFloatStorageFormats(t *testing.T) {
	src := floatStorageProgram
	src = replaceOnce(src, "sqrtf: (x: c.Float): c.Float = c.extern(\"sqrtf\")\n", "")
	src = replaceOnce(src, "  score = f32(sqrtf(c.Float(two))) == sqrt(two) ? score + 1 | score\n", "")
	if got := interpretChecked(t, src); got != floatStorageScore-1 {
		t.Fatalf("interpreter scored %d of %d checks", got, floatStorageScore-1)
	}
}

func replaceOnce(s, old, replacement string) string {
	for i := 0; i+len(old) <= len(s); i++ {
		if s[i:i+len(old)] == old {
			return s[:i] + replacement + s[i+len(old):]
		}
	}
	return s
}
