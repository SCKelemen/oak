package compiler

import (
	"strings"
	"testing"
)

// Conversions of constants in global initializers (ml finding F19,
// docs/spec/60-effects-allocation.md section 10a): a named conversion or a
// float constructor over constants is folded by the backend, so a
// quantization table or a rounded threshold can be static storage, and a
// constant global may be read by the constant initializers after it. The
// compiled program reads the folded values; the interpreter computes the
// same ones at load.
const globalConstantsProgram = `
Limits: type = struct {
  half: f16
  scale: f32
  byte: u8
}

HALF: f16 = f16_round_f32(0.5)
HALF_BITS: u16 = u16_bits_f16(f16_round_f32(0.5))
NEXT_BITS: u16 = u16_bits_f16(f16_round_f32(0.5)) + u16(1)
SCALE: f32 = f32_round_i32(3)
ONE: f32 = f32(f16_bits_u16(u16(15360)))
WIDE: f64 = f64(0x1p-140)
NARROW: u8 = u8_trunc_u32(u32(300))
SIGNED: i32 = i32_bits_u32(u32(4294967295))
CLAMPED: f8e4m3 = f8e4m3_saturating_f32(1000.0)
INF: f32 = f32_round_f64(1e300)
NEGATIVE: f32 = -f32_round_i32(2)
LIMITS: Limits = Limits { half: f16_round_f32(1.5), scale: f32_round_i32(4), byte: u8_saturating_u32(u32(300)) }
TABLE: [4]bf16 = [4]bf16{ bf16_round_f32(1.0), bf16_round_f32(0x1.01p0), bf16_round_f32(0x1.018p0), bf16_round_f32(-2.0) }
ROWS: u32 = u32(6)
COLS: u32 = u32(7)
CELLS: u32 = ROWS * COLS
LAST: u32 = CELLS - u32(1)
SCALED: f32 = f32_round_u32(CELLS) * 0.5

checks: (): u32 {
  score: u32 = 0
  score = f32(HALF) == 0.5 ? score + 1 | score
  score = HALF_BITS == u16(14336) ? score + 1 | score
  score = NEXT_BITS == u16(14337) ? score + 1 | score
  score = SCALE == 3.0 ? score + 1 | score
  score = ONE == 1.0 ? score + 1 | score
  score = WIDE == 0x1p-140 ? score + 1 | score
  score = NARROW == u8(44) ? score + 1 | score
  score = SIGNED == -1 ? score + 1 | score
  score = u8_bits_f8e4m3(CLAMPED) == u8(126) ? score + 1 | score
  score = is_infinite(INF) ? score + 1 | score
  score = NEGATIVE == -2.0 ? score + 1 | score
  score = f32(LIMITS.half) == 1.5 && LIMITS.scale == 4.0 && LIMITS.byte == u8(255) ? score + 1 | score
  score = u16_bits_bf16(TABLE[0]) == u16(16256) && u16_bits_bf16(TABLE[1]) == u16(16256) ? score + 1 | score
  score = u16_bits_bf16(TABLE[2]) == u16(16257) && f32(TABLE[3]) == -2.0 ? score + 1 | score
  score = CELLS == u32(42) && LAST == u32(41) && SCALED == 21.0 ? score + 1 | score
  score
}

main: (): i32 {
  i32_bits_u32(checks())
}
`

const globalConstantsScore = 15

func TestE2EGlobalConstantConversions(t *testing.T) {
	code, abnormal := buildAndRun(t, "globalconstants", globalConstantsProgram)
	if abnormal {
		t.Fatalf("compiled program trapped")
	}
	if code != globalConstantsScore {
		t.Fatalf("compiled program scored %d of %d checks", code, globalConstantsScore)
	}
}

func TestInterpreterGlobalConstantConversions(t *testing.T) {
	if got := interpretChecked(t, globalConstantsProgram); got != globalConstantsScore {
		t.Fatalf("interpreter scored %d of %d checks", got, globalConstantsScore)
	}
}

// A folded initializer is a compile-time constant, so OAK-T0501 does not
// warn on it; a call to an ordinary function still does.
func TestGlobalConstantConversionsDoNotWarn(t *testing.T) {
	model, err := New().WithSource("g.oak", globalConstantsProgram).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	for _, d := range model.TypeChecker.Diagnostics() {
		if strings.Contains(d.Code, "T0501") {
			t.Fatalf("folded global warned: %s", d.Message)
		}
	}
}
