package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
)

// Views, spans, and subslice in the interpreter mirror the backend: a view
// reads through to its owner, a span writes through, subslice derives a
// window with one non-overflowing check, and out-of-range derivation or
// access is an error (the interpreter's trap).
func TestViewsSpansAndSubslice(t *testing.T) {
	result := testEval(`
regs: [4]u64
regs[u32(1)] = u64(40)
regs[u32(2)] = u64(2)
v: []u64 = view(&regs)
rest: []u64 = subslice(v, u32(1), u32(2))
total: u64 = rest[u32(0)] + rest[u32(1)]
s: [*]u64 = span(&regs)
tail: [*]u64 = subslice(s, u32(2), u32(2))
tail[u32(1)] = u64(7)
total + regs[u32(3)] + u64(len(rest))
`)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 51 {
		t.Fatalf("expected 51 (40 + 2 + 7 + 2), got %s", result.Inspect())
	}

	for name, src := range map[string]string{
		"derive past the end": "regs: [4]u64\nv: []u64 = view(&regs)\nsubslice(v, u32(3), u32(2))",
		"index past the end":  "regs: [4]u64\nv: []u64 = view(&regs)\nrest: []u64 = subslice(v, u32(1), u32(2))\nrest[u32(2)]",
		"store through view":  "regs: [4]u64\nv: []u64 = view(&regs)\nv[u32(0)] = u64(1)",
	} {
		out := testEval(src)
		if err, isErr := out.(*object.Error); !isErr || !strings.Contains(err.Message, "out of") && !strings.Contains(err.Message, "read-only") {
			t.Fatalf("%s must be an interpreter error, got %s", name, out.Inspect())
		}
	}
}
