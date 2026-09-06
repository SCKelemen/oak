package evaluator

import (
	"testing"

	"github.com/SCKelemen/oak/object"
)

// Interpreter parity for the portable simd library
// (docs/spec/93-simd.md section 1.3): the interpreter realizes the exact
// Oak.Simd lane semantics — the third witness alongside the NEON and
// portable C lowerings.
func TestSimdInterpreterParity(t *testing.T) {
	boolTests := []struct {
		input string
		want  bool
	}{
		// The byte-search law: any(eq(a, b)) iff some lane matches.
		{"simd.any_u8x16(simd.eq_u8x16(simd.splat_u8x16(u8(7)), simd.splat_u8x16(u8(7))))", true},
		{"simd.any_u8x16(simd.eq_u8x16(simd.splat_u8x16(u8(7)), simd.splat_u8x16(u8(9))))", false},
		// Masks are two-valued: xor of equal vectors is all-zero.
		{"simd.any_u32x4(simd.xor_u32x4(simd.splat_u32x4(u32(3)), simd.splat_u32x4(u32(3))))", false},
		{"simd.all_u64x2(simd.eq_u64x2(simd.splat_u64x2(u64(5)), simd.splat_u64x2(u64(5))))", true},
		// min/max are lane-wise unsigned.
		{"simd.all_u64x2(simd.eq_u64x2(simd.max_u64x2(simd.splat_u64x2(u64(5)), simd.splat_u64x2(u64(9))), simd.splat_u64x2(u64(9))))", true},
		{"simd.all_u16x8(simd.eq_u16x8(simd.min_u16x8(simd.splat_u16x8(u16(5)), simd.splat_u16x8(u16(9))), simd.splat_u16x8(u16(5))))", true},
	}
	for _, tt := range boolTests {
		result := testEval(tt.input)
		boolean, ok := result.(*object.Boolean)
		if !ok {
			t.Fatalf("%s: expected Bool, got %v", tt.input, result)
		}
		if boolean.Value != tt.want {
			t.Fatalf("%s = %v, want %v", tt.input, boolean.Value, tt.want)
		}
	}

	intTests := []struct {
		input string
		want  int64
	}{
		// Wrapping lane addition: 200 + 100 wraps mod 256 to 44.
		{"arm64.uaddlv_u8x16(simd.add_u8x16(simd.splat_u8x16(u8(200)), simd.splat_u8x16(u8(100))))", 16 * 44},
		// Horizontal instructions over crafted lanes.
		{"arm64.uaddlv_u8x16(simd.splat_u8x16(u8(66)))", 16 * 66},
		{"arm64.umaxv_u8x16(simd.max_u8x16(simd.splat_u8x16(u8(65)), simd.splat_u8x16(u8(66))))", 66},
		{"arm64.uminv_u8x16(simd.min_u8x16(simd.splat_u8x16(u8(65)), simd.splat_u8x16(u8(66))))", 65},
		// CNT: popcount of 0xFF is 8 per lane.
		{"arm64.uaddlv_u8x16(arm64.cnt_u8x16(simd.splat_u8x16(u8(255))))", 128},
	}
	for _, tt := range intTests {
		result := testEval(tt.input)
		integer, ok := result.(*object.Integer)
		if !ok {
			t.Fatalf("%s: expected integer, got %v", tt.input, result)
		}
		if integer.Value != tt.want {
			t.Fatalf("%s = %d, want %d", tt.input, integer.Value, tt.want)
		}
	}
}
