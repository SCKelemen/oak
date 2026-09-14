package typechecker

import (
	"strings"
	"testing"
)

// A bounded quantifier is Bool, binds its names for the body only, and
// ranges over finite domains (docs/spec/10-syntax.md section 3e).
func TestQuantifierExpressionTypes(t *testing.T) {
	tests := []struct {
		input string
		err   string
	}{
		{"f: (y: u8): Bool = forall (x: u8) { x + y == y + x }", ""},
		{"Color: type = Red | Green | Blue\nf: (): Bool = exists (c: Color) { c == .Blue }", ""},
		{"f: (): Bool = forall (a: Bool, b: i16) { a || b < i16(0) || b >= i16(0) }", ""},
		{"f: (): Bool = forall (x: u32) { x == x }", "more than 65536 values"},
		{"f: (): Bool = forall (x: u8) { x }", "a quantifier body is Bool, not u8"},
		{"f: (): u8 = forall (x: u8) { x == x }", "expected return type u8, got Bool"},
		{"f: (): Bool {\n  forall (x: u8) { x == x }\n  x == u8(1)\n}", "undefined"},
		{"Shape: type = Dot | Line: u8\nf: (): Bool = forall (s: Shape) { s == .Dot }", "carries a payload"},
	}
	for _, tt := range tests {
		tc := setupTypeChecker(tt.input)
		tc.CheckProgram(parseProgram(tt.input))
		joined := strings.Join(tc.Errors(), "\n")
		if tt.err == "" && joined != "" {
			t.Errorf("%s: unexpected errors:\n%s", tt.input, joined)
		}
		if tt.err != "" && !strings.Contains(joined, tt.err) {
			t.Errorf("%s: want an error containing %q, got:\n%s", tt.input, tt.err, joined)
		}
	}
}
