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

// assert (docs/spec/85-discipline.md section 5): one Bool argument, unit
// result, always compiled in.
func TestAssertBuiltinTypeChecks(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		hasError bool
	}{
		{"bool condition accepted", "x: i32 = 5\nassert(x == 5)", false},
		{"non-bool condition rejected", "x: i32 = 5\nassert(x)", true},
		{"arity enforced", "assert(true, false)", true},
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

// Closure capture discipline (docs/spec/60-effects-allocation.md section 10,
// Oak.ClosureCapture): captureless function literals are legal code
// pointers; capturing closures are rejected until environment storage can be
// justified explicitly.
func TestClosureCaptureDiscipline(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		wantCode bool
	}{
		{"captureless literal accepted", "f := fn(x, y) { x + y }", false},
		{"capturing an outer local rejected", "n: i32 = 1\nf := fn(x) { x + n }", true},
		{"parameter shadowing is not capture", "n: i32 = 1\nf := fn(n) { n + 1 }", false},
		{"top-level function reference is not capture", "fn helper(a: i32) -> i32 { a }\nf := fn(x) { helper(x) }", false},
		{"nested literal parameters are not captures", "f := fn(x) { g := fn(y) { y + x }\nx }", true},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tc := setupTypeChecker(tt.input)
			program := parseProgram(tt.input)
			tc.CheckProgram(program)
			count := 0
			for _, d := range tc.Diagnostics() {
				if d.Code == CodeClosureCaptureStorage {
					count++
				}
			}
			if tt.wantCode && count != 1 {
				t.Errorf("input %q: expected exactly one %s, got %d (%v)", tt.input, CodeClosureCaptureStorage, count, tc.Errors())
			}
			if !tt.wantCode && count != 0 {
				t.Errorf("input %q: unexpected %s: %v", tt.input, CodeClosureCaptureStorage, tc.Errors())
			}
		})
	}
}
