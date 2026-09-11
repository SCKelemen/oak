package evaluator

import (
	"testing"

	"github.com/SCKelemen/oak/object"
)

// The interpreter's assert_eq/assert_ne name both values exactly as the
// compiled helper does (docs/spec/85-discipline.md section 5).
func TestAssertValuesInterpreter(t *testing.T) {
	if got := testEval("assert_eq(2 + 3, 5)\nassert_ne(true, false)\n42"); got == nil || got.Inspect() != "42" {
		t.Fatalf("passing assertions must be silent, got %v", got)
	}
	cases := []struct{ src, want string }{
		{"assert_eq(2 + 3, 4)", "assertion failed: got 5, want 4"},
		{"assert_ne(7, 7)", "assertion failed: got 7, want anything but 7"},
		{"assert_eq(true, false)", "assertion failed: got true, want false"},
		{"assert_eq(1, true)", "assert_eq operands must have one type, got INTEGER and BOOLEAN"},
	}
	for _, c := range cases {
		got := testEval(c.src)
		err, ok := got.(*object.Error)
		if !ok || err.Message != c.want {
			t.Fatalf("%s: got %v, want error %q", c.src, got, c.want)
		}
	}
}
