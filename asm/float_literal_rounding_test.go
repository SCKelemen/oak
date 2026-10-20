package asm

import (
	"fmt"
	"math"
	"strconv"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// Literal admission must use the original text at the context's width.
// These expected bits are fixed independently of the parser's f64 cache.
func TestSourceFloatLiteralRounding(t *testing.T) {
	cases := []struct {
		name, text string
		width      int
		bits       uint64
	}{
		{"above_even_midpoint", "1.00000005960464477550", 32, 0x3f800001},
		{"below_odd_midpoint", "1.00000017881393432617", 32, 0x3f800001},
		{"even_midpoint", "1.000000059604644775390625", 32, 0x3f800000},
		{"odd_midpoint", "1.000000178813934326171875", 32, 0x3f800002},
		{"decimal_exponent", "100000005960464477550e-20", 32, 0x3f800001},
		{"hex_above_midpoint", "0x1.00000100000000000001p0", 32, 0x3f800001},
		{"hex_midpoint", "0x1.000001p0", 32, 0x3f800000},
		{"exact", "1.5", 32, 0x3fc00000},
		{"zero", "0.0", 32, 0},
		{"underflow", "1e-100", 32, 0},
		{"least_subnormal", "0x1p-149", 32, 1},
		{"subnormal_midpoint", "0x1p-150", 32, 0},
		{"above_subnormal_midpoint", "0x1.0000000000000001p-150", 32, 1},
		{"normal_boundary_midpoint", "0x0.ffffffp-126", 32, 0x00800000},
		{"below_normal_boundary_midpoint", "0x0.fffffeffffffffffffffp-126", 32, 0x007fffff},
		{"max_finite", "0x1.fffffep127", 32, 0x7f7fffff},
		{"below_overflow_midpoint", "0x1.fffffeffffffffffffffp127", 32, 0x7f7fffff},
		{"binary64_witness", "1.00000005960464477550", 64, 0x3ff0000010000000},
		{"binary64_exact", "1.5", 64, 0x3ff8000000000000},
		{"binary64_subnormal", "0x1p-1074", 64, 1},
		{"binary64_underflow", "1e-400", 64, 0},
	}
	for _, tc := range cases {
		for _, negative := range []bool{false, true} {
			name, text, want := tc.name, tc.text, tc.bits
			if negative {
				name, text = "negative_"+name, "-"+text
				want ^= uint64(1) << uint(tc.width-1)
			}
			t.Run(name, func(t *testing.T) {
				spec, err := parseSignatureWithBody(fmt.Sprintf("f: (a: f%d) -> f%d = %s", tc.width, tc.width, text))
				if err != nil {
					t.Fatal(err)
				}
				got, reason, ok := newLowering(spec).lower(spec.Body, tc.width)
				if !ok {
					t.Fatalf("not lowered: %s", reason)
				}
				if got.kind != termConst || got.width != tc.width || got.value != want {
					t.Fatalf("%s at f%d: got %s (0x%x), want 0x%x", text, tc.width, got, got.value, want)
				}
			})
		}
	}
}

func TestSourceFloatLiteralDoubleRoundingWitness(t *testing.T) {
	const text = "1.00000005960464477550"
	direct, err := strconv.ParseFloat(text, 32)
	if err != nil {
		t.Fatal(err)
	}
	cached, err := strconv.ParseFloat(text, 64)
	if err != nil {
		t.Fatal(err)
	}
	if got := math.Float32bits(float32(direct)); got != 0x3f800001 {
		t.Fatalf("direct rounding: got 0x%x", got)
	}
	if got := math.Float32bits(float32(cached)); got != 0x3f800000 {
		t.Fatalf("double rounding: got 0x%x", got)
	}
}

// The public verifier must prove the correct bits and reject the cached-f64
// result. Loading an integer bit pattern avoids any assembler decimal parser.
func TestVerifySourceFloatLiteralRounding(t *testing.T) {
	for _, tc := range []struct {
		name, literal string
		bits          uint32
	}{
		{"positive", "1.00000005960464477550", 0x3f800001},
		{"negative", "-1.00000005960464477550", 0xbf800001},
	} {
		for _, correct := range []bool{true, false} {
			bits, want := tc.bits, VerdictProven
			if !correct {
				bits, want = bits-1, VerdictMismatch
			}
			t.Run(fmt.Sprintf("%s/correct_%t", tc.name, correct), func(t *testing.T) {
				decl := "rounded: (a: f32) -> f32"
				arm := fmt.Sprintf("  bind s0 = a\n  clobber w9\n  movz w9, #%d\n  movk w9, #%d, lsl #16\n  fmov s0, w9\n  ret", bits&0xffff, bits>>16)
				if v := verifyCase(t, decl, tc.literal, arm); v.Kind != want {
					t.Errorf("ARM64: got %s: %s; want %s", v.Kind, v.Message, want)
				}
				rv := fmt.Sprintf("  bind fa0 = a\n  clobber t0\n  li t0, %d\n  fmv.w.x fa0, t0\n  ret", int32(bits))
				if v := rv64Verify(t, decl, tc.literal, rv); v.Kind != want {
					t.Errorf("RV64: got %s: %s; want %s", v.Kind, v.Message, want)
				}
			})
		}
	}
}

func TestSourceFloatLiteralInvalidFailsClosed(t *testing.T) {
	spec, err := parseSignatureWithBody("f: (a: f32) -> f32 = a")
	if err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		text  string
		width int
	}{
		{"1e39", 32},
		{"0x1.ffffffp127", 32},
		{"1e400", 64},
		{"not-a-number", 32},
		{"", 32},
		{"1.5", 16},
	} {
		t.Run(fmt.Sprintf("%s/f%d", tc.text, tc.width), func(t *testing.T) {
			// A stale or synthetic Value must never substitute for invalid Text.
			lit := &ast.FloatLiteral{Text: tc.text, Value: 1.5}
			if got, reason, ok := newLowering(spec).lower(lit, tc.width); ok || got != nil || reason == "" {
				t.Fatalf("invalid literal admitted: term=%v reason=%q ok=%t", got, reason, ok)
			}
		})
	}
}
