package evaluator

import "testing"

// Bounded quantifiers enumerate their finite domains and stop at the
// deciding assignment (docs/spec/10-syntax.md section 3e).
func TestEvalQuantifiers(t *testing.T) {
	tests := []struct {
		input string
		want  bool
	}{
		{"forall (b: Bool) { b || !b }", true},
		{"exists (b: Bool) { b && !b }", false},
		{"exists (x: u8) { x == u8(200) }", true},
		{"forall (x: i8) { x < i8(100) }", false},
		{"forall (x: i8) { x >= i8(-128) }", true},
		{"forall (x: u16) { x + u16(1) - u16(1) == x }", true},
		{"exists (x: u16) { x == u16(65535) }", true},
		{"forall (x: u8, y: u8) { x + y == y + x }", true},
		{"exists (x: u8, y: u8) { x + y == u8(3) && x > y }", true},
		{"Color: type = Red | Green | Blue\nexists (c: Color) { c == .Blue }", true},
		{"Color: type = Red | Green | Blue\nforall (c: Color) { c == .Blue }", false},
		// The words stay identifiers outside the binder form.
		{"exists: u8 = u8(3)\nforall: u8 = u8(4)\nexists + forall == u8(7)", true},
	}
	for _, tt := range tests {
		val := testEval(tt.input)
		if !testBoolObj(t, val, tt.want) {
			t.Errorf("%s: got %v", tt.input, val)
		}
	}
}
