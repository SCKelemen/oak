package compiler

// The mx package (stdlib/mx.oak): the OCP Microscaling MXFP4 block format
// in Oak, checked against the format definition (every E2M1 code, the
// rounding ties, the E8M0 scale range) and, over a sweep of pseudo-random
// blocks, against a Go reference of the same quantization. The same program
// runs compiled and interpreted and must agree with both.

import (
	"fmt"
	"math"
	"testing"
)

func fp4WidenReference(code uint8) float32 {
	magnitudes := [8]float32{0, 0.5, 1, 1.5, 2, 3, 4, 6}
	m := magnitudes[code&7]
	if code&8 != 0 {
		return -m
	}
	return m
}

func fp4RoundReference(x float32) uint8 {
	bits := math.Float32bits(x)
	sign := uint32(bits>>28) & 8
	exp := (bits >> 23) & 255
	mant := bits & 0x7FFFFF
	switch {
	case exp == 255:
		if mant != 0 {
			return 0
		}
		return uint8(sign | 7)
	case exp >= 130:
		return uint8(sign | 7)
	case exp <= 126:
		if exp < 125 {
			return uint8(sign)
		}
		shift := 149 - exp
		full := mant | 0x800000
		code := full >> shift
		rem := full & (1<<shift - 1)
		midpoint := uint32(1) << (shift - 1)
		if rem > midpoint || (rem == midpoint && code&1 == 1) {
			code++
		}
		return uint8(sign | code)
	}
	code := (exp-126)<<1 | mant>>22
	rem := mant & 0x3FFFFF
	if rem > 0x200000 || (rem == 0x200000 && code&1 == 1) {
		code++
	}
	if code > 7 {
		code = 7
	}
	return uint8(sign | code)
}

func e8m0WidenReference(code uint8) float32 {
	switch code {
	case 255:
		return math.Float32frombits(0x7FC00000)
	case 0:
		return math.Float32frombits(0x00400000)
	}
	return math.Float32frombits(uint32(code) << 23)
}

func fp4ScaleReference(values [32]float32) uint8 {
	largest := float32(0)
	for _, v := range values {
		m := float32(math.Abs(float64(v)))
		if m > largest {
			largest = m
		}
	}
	exp := (math.Float32bits(largest) >> 23) & 255
	switch {
	case largest == 0 || exp == 255:
		return 127
	case exp <= 2:
		return 0
	}
	return uint8(exp - 2)
}

func fp4QuantizeReference(values [32]float32) (uint8, [16]uint8) {
	scale := fp4ScaleReference(values)
	inverse := e8m0WidenReference(254 - scale)
	var packed [16]uint8
	for i := 0; i < 16; i++ {
		low := fp4RoundReference(values[2*i] * inverse)
		high := fp4RoundReference(values[2*i+1] * inverse)
		packed[i] = low | high<<4
	}
	return scale, packed
}

func fp4DequantizeReference(scale uint8, packed [16]uint8) [32]float32 {
	var out [32]float32
	for i := 0; i < 32; i++ {
		code := packed[i>>1]
		if i&1 == 0 {
			code &= 15
		} else {
			code >>= 4
		}
		out[i] = e8m0WidenReference(scale) * fp4WidenReference(code)
	}
	return out
}

// The sweep's block generator: an LCG whose words become f32 values with
// exponents 100..163 (magnitudes 2^-27 through 2^36, every sign), one word
// in sixteen zeroed so blocks carry exact zeros too.
func mxSample(r uint32) float32 {
	if r&15 == 0 {
		return 0
	}
	return math.Float32frombits(r&0x807FFFFF | (100+(r>>23)&63)<<23)
}

func mxSweepReference() uint32 {
	h := uint32(2166136261)
	mix := func(b uint8) { h = (h ^ uint32(b)) * 16777619 }
	seed := uint32(12345)
	for b := 0; b < 64; b++ {
		var values [32]float32
		for i := range values {
			seed = seed*1664525 + 1013904223
			values[i] = mxSample(seed)
		}
		scale, packed := fp4QuantizeReference(values)
		mix(scale)
		for _, p := range packed {
			mix(p)
		}
		for _, v := range fp4DequantizeReference(scale, packed) {
			u := math.Float32bits(v)
			mix(uint8(u >> 24))
			mix(uint8(u >> 16))
			mix(uint8(u >> 8))
			mix(uint8(u))
		}
	}
	return h
}

// mxProgram scores the checks and exits 42 when every one of `total`
// passed; the interpreter run drops the layout check, which is
// compile-time only.
func mxProgram(expectedSweep uint32, total int) string {
	return fmt.Sprintf(`import("mx")

mix: (h: u32, b: u8): u32 = (h ^ u32(b)) * u32(16777619)

next: (seed: u32): u32 = seed * u32(1664525) + u32(1013904223)

sample: (r: u32): f32 {
  (r & u32(15)) == u32(0) ? 0.0 |
  f32_bits_u32((r & u32(2155872255)) | ((u32(100) + ((r >> u32(23)) & u32(63))) << u32(23)))
}

sweep: (): u32 {
  h: u32 = u32(2166136261)
  seed: u32 = u32(12345)
  b: u32 = 0
  while b < u32(64) {
    values: [32]f32
    i: u32 = 0
    while i < u32(32) {
      seed = next(seed)
      values[i] = sample(seed)
      i = i + u32(1)
    }
    block: mx.Fp4Block = mx.fp4_quantize(values)
    h = mix(h, block.scale)
    i = 0
    while i < u32(16) {
      h = mix(h, block.packed[i])
      i = i + u32(1)
    }
    back: [32]f32 = mx.fp4_dequantize(block)
    i = 0
    while i < u32(32) {
      u: u32 = u32_bits_f32(back[i])
      h = mix(h, u8_trunc_u32(u >> u32(24)))
      h = mix(h, u8_trunc_u32(u >> u32(16)))
      h = mix(h, u8_trunc_u32(u >> u32(8)))
      h = mix(h, u8_trunc_u32(u))
      i = i + u32(1)
    }
    b = b + u32(1)
  }
  h
}

checks: (): u32 {
  score: u32 = 0
  // Every code widens to its magnitude with its sign.
  score = mx.fp4_widen(u8(0)) == 0.0 && mx.fp4_widen(u8(1)) == 0.5 && mx.fp4_widen(u8(2)) == 1.0 && mx.fp4_widen(u8(3)) == 1.5 ? score + 1 | score
  score = mx.fp4_widen(u8(4)) == 2.0 && mx.fp4_widen(u8(5)) == 3.0 && mx.fp4_widen(u8(6)) == 4.0 && mx.fp4_widen(u8(7)) == 6.0 ? score + 1 | score
  score = mx.fp4_widen(u8(9)) == -0.5 && mx.fp4_widen(u8(15)) == -6.0 && u32_bits_f32(mx.fp4_widen(u8(8))) == u32(2147483648) ? score + 1 | score
  // Rounding: ties to even on the E2M1 grid (0.25 -> 0, 0.75 -> 1.0,
  // 1.25 -> 1.0, 1.75 -> 2.0, 2.5 -> 2.0, 3.5 -> 4.0, 5.0 -> 4.0), 6 and
  // beyond clamp to 6, NaN is zero, infinities clamp with their sign.
  score = mx.fp4_round_f32(0.25) == u8(0) && mx.fp4_round_f32(0.26) == u8(1) && mx.fp4_round_f32(0.125) == u8(0) ? score + 1 | score
  score = mx.fp4_round_f32(0.75) == u8(2) && mx.fp4_round_f32(0.7) == u8(1) && mx.fp4_round_f32(0.8) == u8(2) ? score + 1 | score
  score = mx.fp4_round_f32(1.25) == u8(2) && mx.fp4_round_f32(1.75) == u8(4) && mx.fp4_round_f32(2.5) == u8(4) ? score + 1 | score
  score = mx.fp4_round_f32(3.5) == u8(6) && mx.fp4_round_f32(5.0) == u8(6) && mx.fp4_round_f32(5.1) == u8(7) ? score + 1 | score
  score = mx.fp4_round_f32(6.0) == u8(7) && mx.fp4_round_f32(100.0) == u8(7) && mx.fp4_round_f32(-3.0) == u8(13) ? score + 1 | score
  quiet_nan: f32 = f32_bits_u32(u32(2143289344))
  pos_inf: f32 = f32_bits_u32(u32(2139095040))
  score = mx.fp4_round_f32(quiet_nan) == u8(0) && mx.fp4_round_f32(pos_inf) == u8(7) && mx.fp4_round_f32(-pos_inf) == u8(15) ? score + 1 | score
  // E8M0: 1.0 is 127, the ends are 2^-127 and 2^127, 0xFF is NaN.
  score = mx.e8m0_widen(u8(127)) == 1.0 && mx.e8m0_widen(u8(1)) == 0x1p-126 && mx.e8m0_widen(u8(128)) == 2.0 ? score + 1 | score
  score = mx.e8m0_widen(u8(0)) == 0x1p-127 && mx.e8m0_widen(u8(254)) == 0x1p127 && is_nan(mx.e8m0_widen(u8(255))) ? score + 1 | score
  // A block of quarter steps 0 .. 7.75 has largest 7.75 (2^2 .. 2^3), so
  // the scale is 1; elements round on the bare grid.
  ramp: [32]f32
  i: u32 = 0
  while i < u32(32) {
    ramp[i] = f32_round_u32(i) * 0.25
    i = i + u32(1)
  }
  block: mx.Fp4Block = mx.fp4_quantize(ramp)
  score = block.scale == u8(127) ? score + 1 | score
  score = mx.fp4_get(block, u32(1)) == 0.0 && mx.fp4_get(block, u32(3)) == 1.0 && mx.fp4_get(block, u32(4)) == 1.0 ? score + 1 | score
  score = mx.fp4_get(block, u32(31)) == 6.0 && mx.fp4_get(block, u32(12)) == 3.0 && mx.fp4_get(block, u32(0)) == 0.0 ? score + 1 | score
  // Elements 2 and 3 (0.5 and the tie 0.75) pack as codes 1 and 2.
  score = block.packed[0] == u8(0) && block.packed[1] == u8(33) ? score + 1 | score
  // Largest 100 scales by 16 (code 131): 100 / 16 rounds to 6, back to 96;
  // 40 / 16 is the tie 2.5 and rounds to the even 2, back to 32; -1 / 16 is
  // 0.0625 and rounds to zero.
  wide: [32]f32
  wide[5] = 100.0
  wide[6] = -1.0
  wide[7] = 40.0
  scaled: mx.Fp4Block = mx.fp4_quantize(wide)
  score = scaled.scale == u8(131) && mx.fp4_get(scaled, u32(5)) == 96.0 && mx.fp4_get(scaled, u32(6)) == 0.0 ? score + 1 | score
  score = mx.fp4_get(scaled, u32(7)) == 32.0 && mx.fp4_get(scaled, u32(0)) == 0.0 ? score + 1 | score
  back: [32]f32 = mx.fp4_dequantize(scaled)
  score = back[5] == 96.0 && back[7] == 32.0 && back[31] == 0.0 ? score + 1 | score
  // An all-zero block scales by 1; a block whose largest value is the
  // smallest subnormal takes the smallest scale and quantizes to zero.
  zero: [32]f32
  score = mx.fp4_quantize(zero).scale == u8(127) ? score + 1 | score
  tiny: [32]f32
  tiny[9] = f32_bits_u32(u32(1))
  score = mx.fp4_quantize(tiny).scale == u8(0) && mx.fp4_get(mx.fp4_quantize(tiny), u32(9)) == 0.0 ? score + 1 | score
  // Layout: seventeen bytes, the scale first.
  score = size_of[mx.Fp4Block]() == 17 && offset_of[mx.Fp4Block](packed) == 1 ? score + 1 | score
  score = sweep() == u32(%d) ? score + 1 | score
  score
}

main: (): i32 {
  checks() == u32(%d) ? 42 | i32_bits_u32(checks())
}
`, expectedSweep, total)
}

const mxLayoutCheck = "  score = size_of[mx.Fp4Block]() == 17 && offset_of[mx.Fp4Block](packed) == 1 ? score + 1 | score\n"

func TestE2EMxBlocks(t *testing.T) {
	compiled := mxProgram(mxSweepReference(), 22)
	interpreted := replaceOnce(compiled, mxLayoutCheck, "")
	if interpreted == compiled {
		t.Fatal("layout check not found in the program")
	}
	runHashProgram(t, "mx", compiled, replaceOnce(interpreted, "u32(22) ? 42", "u32(21) ? 42"))
}

// The reference itself has the format's properties: every E2M1 code round
// trips through its magnitude, and every finite f32 rounds to a code whose
// magnitude is within half a grid step of the clamped input.
func TestMxReferenceProperties(t *testing.T) {
	for code := 0; code < 16; code++ {
		if got := fp4RoundReference(fp4WidenReference(uint8(code))); got != uint8(code) && !(code == 8 && got == 0) {
			t.Errorf("code %d widens to %v which rounds to %d", code, fp4WidenReference(uint8(code)), got)
		}
	}
	for i := 0; i < 65536; i++ {
		x := math.Float32frombits(uint32(i) << 16)
		if math.IsNaN(float64(x)) || math.IsInf(float64(x), 0) {
			continue
		}
		code := fp4RoundReference(x)
		back := float64(fp4WidenReference(code))
		clamped := math.Max(-6, math.Min(6, float64(x)))
		step := 0.5
		if math.Abs(clamped) >= 4 {
			step = 2
		} else if math.Abs(clamped) >= 2 {
			step = 1
		}
		if math.Abs(back-clamped) > step/2 {
			t.Errorf("%v rounds to code %d (%v), off by more than half a step", x, code, back)
		}
	}
}
