package compiler

// The 8-bit storage formats, executed (docs/spec/20-types.md section
// 11.3.1): OCP FP8 E4M3 and E5M2 bit patterns are checked against the
// format definitions in the compiled program and in the interpreter, and a
// sweep of every 8-bit pattern and every f32 upper half is checksummed
// against a Go reference of the same rounding, so the C helpers, the
// interpreter, and the reference agree bit for bit.

import (
	"math"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
)

const f8StorageProgram = `
Pair: type = { lo: f8e4m3, hi: f8e5m2 }

checks: (): u32 {
  score: u32 = 0
  // E4M3: 1.0 = 0x38, -2.0 = 0xC0, 448 (max finite) = 0x7E. 456 rounds
  // down to 448, 464 is the tie and rounds to the even 448, 480 is NaN
  // (0x7F): the format has no infinities.
  score = u8_bits_f8e4m3(f8e4m3_round_f32(1.0)) == u8(56) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(-2.0)) == u8(192) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(448.0)) == u8(126) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(456.0)) == u8(126) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(464.0)) == u8(126) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(480.0)) == u8(127) ? score + 1 | score
  // Subnormals: 2^-9 is the smallest (0x01); 2^-10 ties to even (0);
  // 1.5 * 2^-10 rounds up to 0x01; 2^-11 is below every tie.
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1p-9)) == u8(1) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1p-10)) == u8(0) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1.8p-10)) == u8(1) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1p-11)) == u8(0) ? score + 1 | score
  // Ties to even in the normal range: 1 + 2^-4 is halfway to 1.125 and
  // rounds to the even 0x38; 1 + 3 * 2^-5 rounds up to 0x39.
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1.1p0)) == u8(56) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_round_f32(0x1.18p0)) == u8(57) ? score + 1 | score
  // Saturating: finite overflow clamps to the largest finite value of
  // either sign; NaN stays NaN.
  score = u8_bits_f8e4m3(f8e4m3_saturating_f32(1000.0)) == u8(126) ? score + 1 | score
  score = u8_bits_f8e4m3(f8e4m3_saturating_f32(-1000.0)) == u8(254) ? score + 1 | score
  nan: f32 = f32_bits_u32(u32(2143289344))
  score = u8_bits_f8e4m3(f8e4m3_saturating_f32(nan)) == u8(127) ? score + 1 | score
  score = is_nan(f32(f8e4m3_round_f32(nan))) ? score + 1 | score
  // Widening is exact: 0x01 is 2^-9, 0x7E is 448, 0xFF is NaN.
  score = f32(f8e4m3_bits_u8(u8(1))) == 0x1p-9 ? score + 1 | score
  e: f8e4m3 = f8e4m3_bits_u8(u8(126))
  score = f32(e) == 448.0 ? score + 1 | score
  score = is_nan(f32(f8e4m3_bits_u8(u8(255)))) ? score + 1 | score
  // E5M2: 1.0 = 0x3C, 57344 (max finite) = 0x7B, 65536 overflows to
  // infinity (0x7C), the smallest subnormal 2^-16 is 0x01.
  score = u8_bits_f8e5m2(f8e5m2_round_f32(1.0)) == u8(60) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_round_f32(57344.0)) == u8(123) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_round_f32(65536.0)) == u8(124) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_round_f32(0x1p-16)) == u8(1) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_round_f32(0x1p-17)) == u8(0) ? score + 1 | score
  // Ties: 1.125 is halfway between 1.0 and 1.25 and rounds to 0x3C;
  // 1.1875 rounds up to 0x3D.
  score = u8_bits_f8e5m2(f8e5m2_round_f32(0x1.2p0)) == u8(60) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_round_f32(0x1.3p0)) == u8(61) ? score + 1 | score
  // Saturating clamps finite overflow to 57344 but keeps infinity and NaN.
  inf: f32 = f32_bits_u32(u32(2139095040))
  score = u8_bits_f8e5m2(f8e5m2_saturating_f32(65536.0)) == u8(123) ? score + 1 | score
  score = u8_bits_f8e5m2(f8e5m2_saturating_f32(-65536.0)) == u8(251) ? score + 1 | score
  score = is_infinite(f32(f8e5m2_saturating_f32(inf))) ? score + 1 | score
  score = is_nan(f32(f8e5m2_saturating_f32(nan))) ? score + 1 | score
  score = is_infinite(f32(f8e5m2_round_f32(inf))) ? score + 1 | score
  score = is_nan(f32(f8e5m2_round_f32(nan))) ? score + 1 | score
  m: f8e5m2 = f8e5m2_bits_u8(u8(123))
  score = f32(m) == 57344.0 ? score + 1 | score
  // Layout: one byte each, byte aligned, so a pair packs into two bytes.
  score = size_of[f8e4m3]() == 1 ? score + 1 | score
  score = align_of[f8e5m2]() == 1 ? score + 1 | score
  score = size_of[Pair]() == 2 ? score + 1 | score
  p: Pair = Pair { lo: f8e4m3_round_f32(3.0), hi: f8e5m2_round_f32(3.0) }
  score = f32(p.lo) == 3.0 && f32(p.hi) == 3.0 ? score + 1 | score
  score
}

main: (): i32 {
  i32_bits_u32(checks())
}
`

const f8StorageScore = 37

func TestE2EF8StorageFormats(t *testing.T) {
	code, abnormal := buildAndRun(t, "f8storage", f8StorageProgram)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if code != f8StorageScore {
		t.Fatalf("compiled program scored %d of %d checks", code, f8StorageScore)
	}
}

// The interpreter has no layout introspection; the program is re-run
// without the three size_of/align_of checks.
func TestInterpreterF8StorageFormats(t *testing.T) {
	src := f8StorageProgram
	src = replaceOnce(src, "  score = size_of[f8e4m3]() == 1 ? score + 1 | score\n", "")
	src = replaceOnce(src, "  score = align_of[f8e5m2]() == 1 ? score + 1 | score\n", "")
	src = replaceOnce(src, "  score = size_of[Pair]() == 2 ? score + 1 | score\n", "")
	if got := interpretChecked(t, src); got != f8StorageScore-3 {
		t.Fatalf("interpreter scored %d of %d checks", got, f8StorageScore-3)
	}
}

// f8SweepProgram folds every 8-bit pattern's widening and every f32 upper
// half's four narrowings into one FNV-1a checksum. The upper halves cover
// every exponent, both signs, the subnormal thresholds of both formats,
// infinities, and NaNs; the lower halves are zero, so the round-half cases
// are exercised by the fixed checks above.
const f8SweepProgram = `
mix: (h: u32, b: u8): u32 {
  (h ^ u32(b)) * u32(16777619)
}

sweep: (): u32 {
  h: u32 = u32(2166136261)
  b: u32 = 0
  while b < 256 {
    w4: u32 = u32_bits_f32(f32(f8e4m3_bits_u8(u8_trunc_u32(b))))
    w5: u32 = u32_bits_f32(f32(f8e5m2_bits_u8(u8_trunc_u32(b))))
    h = mix(h, u8_trunc_u32(w4 >> 24))
    h = mix(h, u8_trunc_u32(w4 >> 16))
    h = mix(h, u8_trunc_u32(w4 >> 8))
    h = mix(h, u8_trunc_u32(w4))
    h = mix(h, u8_trunc_u32(w5 >> 24))
    h = mix(h, u8_trunc_u32(w5 >> 16))
    h = mix(h, u8_trunc_u32(w5 >> 8))
    h = mix(h, u8_trunc_u32(w5))
    b = b + 1
  }
  i: u32 = 0
  while i < 65536 {
    x: f32 = f32_bits_u32(i << 16)
    h = mix(h, u8_bits_f8e4m3(f8e4m3_round_f32(x)))
    h = mix(h, u8_bits_f8e4m3(f8e4m3_saturating_f32(x)))
    h = mix(h, u8_bits_f8e5m2(f8e5m2_round_f32(x)))
    h = mix(h, u8_bits_f8e5m2(f8e5m2_saturating_f32(x)))
    i = i + 1
  }
  h
}

main: (): i32 {
  i32_bits_u32(sweep() & u32(255))
}
`

// f8SweepReference is the Go rendering of sweep() over the interpreter's
// conversion functions, which are the reference for the C helpers.
func f8SweepReference() uint32 {
	h := uint32(2166136261)
	mix := func(b uint8) { h = (h ^ uint32(b)) * 16777619 }
	mix32 := func(u uint32) { mix(uint8(u >> 24)); mix(uint8(u >> 16)); mix(uint8(u >> 8)); mix(uint8(u)) }
	for b := 0; b < 256; b++ {
		mix32(math.Float32bits(evaluator.F8E4M3ToFloat32(uint8(b))))
		mix32(math.Float32bits(evaluator.F8E5M2ToFloat32(uint8(b))))
	}
	for i := 0; i < 65536; i++ {
		x := math.Float32frombits(uint32(i) << 16)
		mix(evaluator.Float32ToF8E4M3(x))
		mix(evaluator.Float32ToF8E4M3Saturating(x))
		mix(evaluator.Float32ToF8E5M2(x))
		mix(evaluator.Float32ToF8E5M2Saturating(x))
	}
	return h
}

func TestE2EF8Sweep(t *testing.T) {
	code, abnormal := buildAndRun(t, "f8sweep", f8SweepProgram)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if want := int(f8SweepReference() & 255); code != want {
		t.Fatalf("compiled sweep checksum byte %d, reference %d", code, want)
	}
}

func TestInterpreterF8Sweep(t *testing.T) {
	if got, want := interpretChecked(t, f8SweepProgram), int64(f8SweepReference()&255); got != want {
		t.Fatalf("interpreter sweep checksum byte %d, reference %d", got, want)
	}
}

// TestF8ReferenceProperties pins the format definitions the sweep relies
// on: every widening is exact (rounding it back is the identity), every
// non-NaN pattern widens to a value the rounding reproduces, and the
// saturating forms never produce NaN or infinity from a finite input.
func TestF8ReferenceProperties(t *testing.T) {
	for b := 0; b < 256; b++ {
		p := uint8(b)
		if x := evaluator.F8E4M3ToFloat32(p); !math.IsNaN(float64(x)) && evaluator.Float32ToF8E4M3(x) != p {
			t.Errorf("e4m3 pattern %#x widens to %v which rounds to %#x", p, x, evaluator.Float32ToF8E4M3(x))
		}
		if x := evaluator.F8E5M2ToFloat32(p); !math.IsNaN(float64(x)) && evaluator.Float32ToF8E5M2(x) != p {
			t.Errorf("e5m2 pattern %#x widens to %v which rounds to %#x", p, x, evaluator.Float32ToF8E5M2(x))
		}
	}
	for i := 0; i < 65536; i++ {
		x := math.Float32frombits(uint32(i) << 16)
		if math.IsNaN(float64(x)) || math.IsInf(float64(x), 0) {
			continue
		}
		if s := evaluator.Float32ToF8E4M3Saturating(x); s&0x7F == 0x7F {
			t.Errorf("e4m3 saturating %v produced NaN", x)
		}
		if s := evaluator.Float32ToF8E5M2Saturating(x); s&0x7F >= 0x7C {
			t.Errorf("e5m2 saturating %v produced %#x", x, s)
		}
		if a := float64(math.Abs(float64(x))); a > 448 {
			if evaluator.Float32ToF8E4M3(x)&0x7F != 0x7F && a > 464 {
				t.Errorf("e4m3 %v should be NaN", x)
			}
		}
	}
}
