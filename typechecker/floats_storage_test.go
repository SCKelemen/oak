package typechecker

import (
	"strings"
	"testing"
)

// Storage formats (docs/spec/20-types.md section 11.3.1), hexadecimal
// literals (section 11.3.2), and the c.Float / c.Double rows
// (92-ffi.md section 2.2).
func TestFloatStorageHexAndCRows(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
		wantText string
	}{
		// Storage formats: load, store, widen, round, bits — nothing else.
		{"declare and widen f16", "h: f16 = f16_round_f32(1.5)\nx: f32 = f32(h)", false, ""},
		{"declare and widen bf16", "h: bf16 = bf16_round_f32(1.5)\nx: f32 = f32(h)", false, ""},
		{"storage in arrays", "hs: [4]f16\nx: f32 = f32(hs[0])", false, ""},
		{"bits with u16", "h: f16 = f16_round_f32(1.5)\nb: u16 = u16_bits_f16(h)\nback: f16 = u16_bits_f16(b) == b ? h | u16_bits_f16(b)", true, ""},
		{"bits round trip", "h: bf16 = bf16_round_f32(1.5)\nb: u16 = u16_bits_bf16(h)\nback: bf16 = bf16_bits_u16(b)", false, ""},
		{"no arithmetic", "h: f16 = f16_round_f32(1.5)\ny: f16 = h + h", true, "f16 is a storage format with no arithmetic"},
		{"no comparison", "h: f16 = f16_round_f32(1.5)\nsame: Bool = h == h", true, "f16 is a storage format with no comparison"},
		{"no literals", "h: f16 = 1.5", true, "f16 has no literals"},
		{"no constructor", "h: f16 = f16(1.5)", true, "f16 has no constructor"},
		{"round only from f32", "d: f64 = 1.5\nh: f16 = f16_round_f64(d)", true, "not a conversion the specification defines"},
		{"widen to f64 goes through f32", "h: f16 = f16_round_f32(1.5)\nd: f64 = f64(h)", true, "widens to f32 only"},
		{"round from storage is spelled as widening", "h: f16 = f16_round_f32(1.5)\nx: f32 = f32_round_f16(h)", true, "widens exactly; write f32(x)"},
		{"no intrinsics on storage", "h: f16 = f16_round_f32(1.5)\nx: f16 = sqrt(h)", true, "requires floating-point operands"},
		// Hexadecimal literals.
		{"hex float literal f64", "x: f64 = 0x1.8p1", false, ""},
		{"hex float literal f32", "x: f32 = 0x1p-126", false, ""},
		{"hex float overflow f32", "x: f32 = 0x1p128", true, "does not fit in type f32"},
		{"hex integer stays integer", "x: u32 = 0xFF", false, ""},
		// c.Float / c.Double rows.
		{"c.Float from f32 and back", "x: f32 = 1.5\nc1: c.Float = c.Float(x)\nback: f32 = f32(c1)", false, ""},
		{"c.Double from f64 and back", "x: f64 = 1.5\nc1: c.Double = c.Double(x)\nback: f64 = f64(c1)", false, ""},
		{"c.Float rejects f64", "x: f64 = 1.5\nc1: c.Float = c.Float(x)", true, ""},
		{"extern over c.Float", "sqrtf: (x: c.Float): c.Float = c.extern(\"sqrtf\")\nr: f32 = f32(sqrtf(c.Float(2.0)))", false, ""},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Fatalf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
			if tt.wantText != "" && !strings.Contains(strings.Join(tc.Errors(), "\n"), tt.wantText) {
				t.Fatalf("errors %q do not mention %q", tc.Errors(), tt.wantText)
			}
		})
	}
}
