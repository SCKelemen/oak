package compiler

import (
	"strings"
	"testing"
)

// The view and span structs of an owned array's element are declared at
// file scope before any function, whatever the first use looks like: a
// `view(&s)` nested in a call argument used to place `typedef struct
// oak_view_u32 { ... }` inside the expression, which no C compiler accepts.
func TestE2EViewTypedefPlacedAtFileScope(t *testing.T) {
	program := `main: (): u32 {
  s: [1]u32
  a: u32 = 7
  b: u32 = 5
  u32(u8_trunc_u32(a)) + u32(u8_trunc_u32(b)) + len(view(&s))
}
`
	output, err := New().WithSource("placement.oak", program).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	typedef := strings.Index(output, "typedef struct oak_view_u32 {")
	function := strings.Index(output, "u32 oak_main(")
	if typedef < 0 || function < 0 || typedef > function {
		t.Fatalf("oak_view_u32 must be declared before oak_main (typedef at %d, function at %d):\n%s", typedef, function, output)
	}
	code, abnormal := buildAndRun(t, "view_placement", program)
	if abnormal || code != 13 {
		t.Fatalf("exit = (%d, abnormal=%v), want 13", code, abnormal)
	}
}
