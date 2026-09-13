package compiler

import (
	"strings"
	"testing"
)

// The source-level inliner (compiler/inline.go) keeps three name spaces
// apart under one instance prefix: argument temporaries, the result, and
// the callee's locals. A helper whose locals are named a1 and a2 — BLAKE3's
// quarter round — once collided with the temporaries for arguments 1 and 2
// (`__inl34_a1 already declared`, the dbs pilot's A3); and a helper that
// declares effects, forbids, or takes a function value is not inlined, so
// the effect analysis still sees its call.
func TestE2EInlineNamesStayDistinct(t *testing.T) {
	program := `
quarter: (a: u32, b: u32, c: u32, d: u32): [4]u32 {
  a1: u32 = a + b
  a2: u32 = a1 + c
  r: u32 = a2 ^ d
  [4]u32{ a1, a2, r, d }
}

mix: (x: u32): u32 {
  g0: [4]u32 = quarter(x, x + u32(1), x + u32(2), u32(3))
  g1: [4]u32 = quarter(g0[0], g0[1] + u32(1), g0[2] + u32(2), u32(4))
  g0[0] + g0[1] + g0[2] + g0[3] + g1[0] + g1[1] + g1[2] + g1[3]
}

main: (): i32 {
  i32_bits_u32(mix(u32(5)))
}
`
	want := interpretChecked(t, program)
	code, err := New().WithSource("names.oak", program).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(code, "__inl") {
		t.Fatalf("quarter must be inlined into mix:\n%s", code)
	}
	if _, exit, abnormal := buildAndRunFrom(t, "inline_names", New().WithSource("names.oak", program)); abnormal || int64(exit) != want%256 {
		t.Fatalf("exit = (%d, abnormal=%v), want %d", exit, abnormal, want%256)
	}
	rowed := `
launch: (step: (u32) -> u32 effects { }, x: u32): u32 = step(x)
grow: (n: u32): u32 effects { Memory.Allocate } = n
wrap: (n: u32): u32 = grow(n)
main: (): i32 = 0
`
	code, err = New().WithSource("rowed.oak", rowed).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if strings.Contains(code, "__inl") {
		t.Fatalf("a helper with a rowed parameter or declared effects must keep its calls for the effect analysis:\n%s", code)
	}
}
