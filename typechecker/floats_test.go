package typechecker

import (
	"strings"
	"testing"
)

// Floating-point typing (docs/spec/20-types.md section 11.3): contextual
// literals, same-family operators with f32 -> f64 widening only, explicit
// conversions in the {target}_{op}_{source} scheme, and the intrinsic set.
func TestFloatTyping(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
		wantText string
	}{
		// Literals (section 11.3.2).
		{"f32 literal from context", "x: f32 = 1.5", false, ""},
		{"f64 literal from context", "x: f64 = 2.0e-5", false, ""},
		{"exponent literal", "x: f64 = 1e3", false, ""},
		{"bare literal is f64", "x := 1.5\ny: f64 = x", false, ""},
		{"bare literal is not f32", "x := 1.5\ny: f32 = x", true, "expected type f32, got f64"},
		{"integer literal in float context", "x: f32 = 1", true, "spell it 1.0"},
		{"float literal in integer context", "x: u32 = 1.5", true, "floating-point literal 1.5 in integer context"},
		{"f32 literal overflow", "x: f32 = 1e39", true, "does not fit in type f32"},
		{"f64 literal within range", "x: f64 = 1e39", false, ""},
		{"negated literal", "x: f32 = -1.5", false, ""},
		// Operators (sections 11.3.3, 11.3.5).
		{"arithmetic on one width", "a: f32 = 1.5\nb: f32 = 2.5\nc: f32 = a * b + 1.0", false, ""},
		{"f32 widens to f64", "a: f32 = 1.5\nb: f64 = 2.5\nc: f64 = a + b", false, ""},
		{"f64 does not narrow", "a: f32 = 1.5\nb: f64 = 2.5\nc: f32 = a + b", true, "expected type f32, got f64"},
		{"no modulo on floats", "a: f32 = 1.5\nb: f32 = a % 2.0", true, "operator % is not defined on floating-point types"},
		{"no mixing with integers", "a: f32 = 1.5\nn: u32 = 2\nb: f32 = a * n", true, "requires two floating-point operands"},
		{"no bitwise on floats", "a: f32 = 1.5\nb: f32 = a & 1.0", true, ""},
		{"comparison yields Bool", "a: f32 = 1.5\nb: f32 = 2.5\nless: Bool = a < b\nsame: Bool = a == b", false, ""},
		{"comparison with integer rejected", "a: f32 = 1.5\nn: i32 = 2\nless: Bool = a < n", true, "requires two floating-point operands"},
		{"unary minus", "a: f32 = 1.5\nb: f32 = -a", false, ""},
		// Constructors and conversions (section 11.3.4).
		{"widening constructor", "a: f32 = 1.5\nb: f64 = f64(a)", false, ""},
		{"narrowing constructor rejected", "a: f64 = 1.5\nb: f32 = f32(a)", true, "f32_round_f64"},
		{"integer constructor rejected", "n: i32 = 2\nb: f32 = f32(n)", true, "f32_round_i32"},
		{"round from integer", "n: i32 = 2\nb: f32 = f32_round_i32(n)\nc: f64 = f64_round_u64(u64(7))", false, ""},
		{"round from wider float", "a: f64 = 1.5\nb: f32 = f32_round_f64(a)", false, ""},
		{"round widening rejected", "a: f32 = 1.5\nb: f64 = f64_round_f32(a)", true, "widens; write f64(x)"},
		{"bits reinterpretation", "a: f32 = 1.5\nbits: u32 = u32_bits_f32(a)\nback: f32 = f32_bits_u32(bits)\nwide: u64 = u64_bits_f64(2.5)", false, ""},
		{"bits needs the unsigned partner", "a: f32 = 1.5\nbits: i32 = i32_bits_f32(a)", true, "not a conversion the specification defines"},
		{"bits needs the same width", "a: f32 = 1.5\nbits: u64 = u64_bits_f32(a)", true, "not a conversion the specification defines"},
		{"trunc saturating checked", "Result[T, E]: type = Ok: T | Err: E\nOverflow: type = Overflow\na: f32 = 1.5\ni: i32 = i32_trunc_f32(a)\ns: u8 = u8_saturating_f32(a)\nc: Result[i32, Overflow] = i32_checked_f32(a)", false, ""},
		{"trunc to float rejected", "a: f64 = 1.5\nb: f32 = f32_trunc_f64(a)", true, "not a conversion the specification defines"},
		// Intrinsics (section 11.3.5).
		{"intrinsics on f32", "a: f32 = 1.5\nb: f32 = sqrt(a) + fma(a, a, 1.0) + abs(a) + copysign(a, -1.0) + floor(a) + ceil(a) + trunc(a) + round(a) + round_even(a) + min(a, 2.0) + max(a, 2.0) + min_num(a, 2.0) + max_num(a, 2.0)", false, ""},
		{"predicates yield Bool", "a: f64 = 1.5\nn: Bool = is_nan(a)\nf: Bool = is_finite(a)\ni: Bool = is_infinite(a)\nm: Bool = is_normal(a)\no: Bool = total_order(a, 2.0)", false, ""},
		{"intrinsic widens f32 operand", "a: f32 = 1.5\nb: f64 = 2.5\nc: f64 = max(a, b)", false, ""},
		{"all-literal intrinsic is f64", "c: f64 = sqrt(2.0)", false, ""},
		{"intrinsic on integers rejected", "n: u32 = 4\nc: u32 = sqrt(n)", true, "requires floating-point operands"},
		{"intrinsic arity", "a: f32 = 1.5\nc: f32 = fma(a, a)", true, "takes 3 floating-point argument(s)"},
		{"user function shadows intrinsic", "sqrt: (n: u32): u32 { n }\nc: u32 = sqrt(u32(4))", false, ""},
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

// The checker records float widths by position for the backend and the
// interpreter: literals, intrinsic calls, and arithmetic.
func TestFloatWidthsAreRecorded(t *testing.T) {
	input := "a: f32 = 1.5\nb: f32 = sqrt(a) * 2.0"
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	recorded := 0
	for _, width := range tc.arithmeticTypes {
		if width == "f32" {
			recorded++
		}
	}
	// 1.5, sqrt(...), 2.0, and the product: four f32 records.
	if recorded != 4 {
		t.Fatalf("recorded %d f32 widths, want 4: %v", recorded, tc.arithmeticTypes)
	}
}
