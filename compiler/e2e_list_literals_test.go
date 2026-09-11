package compiler

import (
	"strings"
	"testing"
)

// Bare list literals take their shape from context (docs/spec/10-syntax.md
// section 2c, ml ask 5.4): [1, 2, 3] is a [3]u32 where a [3]u32 is
// expected and a view where a []u32 is expected, in declarations,
// arguments, returns, and fields alike, and the compiled program agrees
// with the interpreter.
func TestE2EListLiteralsFromContext(t *testing.T) {
	src := `
Point: type = struct { x: f32, y: f32 }

sum3: (xs: [3]u32): u32 = xs[0] + xs[1] + xs[2]

total: (xs: []u32): u32 {
  acc: u32 = 0
  i: u32 = 0
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + 1
  }
  acc
}

dims: (shape: []u32): u32 = len(shape)

corners: (): [2]Point = [Point { x: 0.0, y: 0.0 }, Point { x: 1.0, y: 2.0 }]

first_x: (ps: []Point): f32 = ps[0].x

triple: (): [3]u32 = [7, 8, 9]

main: (): i32 {
  xs: [3]u32 = [1, 2, 3]
  view_of: []u32 = [10, 20]
  grid: [2][2]u32 = [[1, 2], [3, 4]]
  weights: [2]f32 = [0.5, 1.5]
  a: u32 = sum3(xs)                      // 6
  b: u32 = sum3([4, 5, 6])               // 15
  c: u32 = total([1, 2, 3, 4])           // 10
  d: u32 = total([]u32{100, 200})        // 300
  e: u32 = dims([28, 28])                // 2
  f: u32 = total(view_of)                // 30
  tr: [3]u32 = triple()
  g: u32 = grid[1][1] + tr[2]            // 13
  h: u32 = weights[0] + weights[1] == 2.0 ? u32(1) | u32(0)
  cs: [2]Point = corners()
  k: u32 = first_x([Point { x: 3.0, y: 0.0 }, cs[1]]) == 3.0 ? u32(1) | u32(0)
  i32_bits_u32(a + b + c + d + e + f + g + h + k) - 378 + 42
}
`
	code, abnormal := buildAndRun(t, "listliterals", src)
	if abnormal || code != 42 {
		t.Fatalf("compiled exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter main() = %d, want 42", got)
	}
	out, err := New().WithSource("listliterals.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"(oak_arr_u32_3){ { 4, 5, 6 } }", "(oak_view_u32){ (u32[]){ 1, 2, 3, 4 }, 4 }", "(oak_view_u32){ (u32[]){ 100, 200 }, 2 }"} {
		if !strings.Contains(out, want) {
			t.Fatalf("emitted C lacks %q", want)
		}
	}
}

// A literal that does not fit its context is rejected with the element
// count or element type named; a literal with no context at all is
// rejected rather than guessed.
func TestListLiteralContextErrors(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"count", "main: (): i32 {\n  xs: [3]u32 = [1, 2]\n  0\n}", "has 2 elements, expected 3"},
		{"count-argument", "sum3: (xs: [3]u32): u32 = xs[0]\nmain: (): i32 {\n  i32_bits_u32(sum3([1, 2]))\n}", "has 2 elements, expected 3"},
		{"element", "main: (): i32 {\n  xs: [2]u32 = [1, 2.5]\n  0\n}", "floating-point literal 2.5 in integer context u32"},
		{"element-type", "main: (): i32 {\n  xs: [2]u32 = [1, true]\n  0\n}", "element 1"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("error = %v, want mention of %q", err, c.want)
			}
		})
	}
}
