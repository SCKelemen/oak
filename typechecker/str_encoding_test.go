package typechecker

import "testing"

// Phantom-encoded strings (docs/spec/70-strings.md, Oak.StrEncoding):
// `string` is Str[Utf8]; encoding tags distinguish static identity while all
// Str[E] share one representation.
func TestPhantomStringEncodings(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{
			"string and Str[Utf8] are the same type",
			"s: Str[Utf8] = \"hi\"\nt: string = s",
			false,
		},
		{
			"Str[Utf8] accepts a string literal",
			"s: Str[Utf8] = \"hi\"",
			false,
		},
		{
			"Str[Ascii] is statically distinct from string",
			"s: Str[Ascii] = \"hi\"",
			true,
		},
		{
			"string cannot flow into Str[Utf16]",
			"s: string = \"hi\"\nu: Str[Utf16] = s",
			true,
		},
		{
			"unknown encoding tag is rejected",
			"s: Str[Latin1] = \"hi\"",
			true,
		},
		{
			"concatenation preserves the canonical string type",
			"a: string = \"x\"\nb: Str[Utf8] = a + \"y\"",
			false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
		})
	}
}

// The unvalidated bytes-to-string path stays closed: reinterpreting a byte
// view as a string-typed binding is rejected (spec section 4 forbids
// from_bytes without validation or an unsafe/proof precondition).
func TestByteViewCannotBecomeString(t *testing.T) {
	inputs := []string{
		"buf: [16]u8\nv: []u8 = buf[0:8]\ns: string = view_as(v)",
		"buf: [16]u8\nv: []u8 = buf[0:8]\ns: string = v",
	}
	for _, input := range inputs {
		tc := setupTypeChecker(input)
		program := parseProgram(input)
		tc.CheckProgram(program)
		if len(tc.Errors()) == 0 {
			t.Errorf("unvalidated bytes flowed into string: %q", input)
		}
	}
}

// rune is the canonical refined u32 (spec section 9): unsigned semantics.
func TestRuneIsUnsigned32(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{"rune accepts full scalar range literal", "r: rune = rune(1114111)", false},
		{"rune widens from u8", "b: u8 = 65\nr: rune = rune(b)", false},
		{"rune does not widen from signed i8", "x: i8 = -1\nr: rune = rune(x)", true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			hasError := len(tc.Errors()) > 0
			if hasError != tt.hasError {
				t.Errorf("input %q: expected error=%v, got errors=%v", tt.input, tt.hasError, tc.Errors())
			}
		})
	}
}
