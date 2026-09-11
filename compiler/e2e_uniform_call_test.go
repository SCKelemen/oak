package compiler

import (
	"strings"
	"testing"
)

// Uniform call syntax (docs/spec/10-syntax.md section 13, ml ask 5.2):
// recv.f(args) is f(recv, args...) when recv's type has no method or field
// named f and a function f is visible at the call site. Chaining reads left
// to right, primitives and records alike are receivers, generic functions
// resolve as for any call, and a method declared for an ADT receiver still
// wins. Compiled and interpreted programs agree.
func TestE2EUniformCallSyntax(t *testing.T) {
	src := `
Vec: type = struct { x: f32, y: f32 }
scale: (v: Vec, k: f32): Vec = Vec { x: v.x * k, y: v.y * k }
norm1: (v: Vec): f32 = v.x + v.y
double: (x: u32): u32 = x + x
first[T]: (xs: []T): T = xs[0]

Shape: type = Dot | Line: u32
length: (s: Shape): u32 = s ? | .Dot => u32(1) | .Line(n) => n

main: (): i32 {
  v: Vec = Vec { x: 1.0, y: 2.0 }
  chained: f32 = v.scale(2.0).norm1()          // norm1(scale(v, 2.0)) = 6
  prim: u32 = u32(21).double()                 // 42
  xs: [3]u32 = [7, 8, 9]
  head: u32 = view(&xs).first()                // first[u32](view(&xs)) = 7
  s: Shape = .Line(u32(5))
  free: u32 = s.length()                       // an ADT receiver: length(s) = 5
  chained == 6.0 && prim == u32(42) && head == u32(7) && free == u32(5) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "uniformcall", src)
	if abnormal || code != 42 {
		t.Fatalf("compiled exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter main() = %d, want 42", got)
	}
	out, err := New().WithSource("uniformcall.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// The lowering is the plain call: no dispatch table, no thunk.
	for _, want := range []string{"oak_norm1( oak_scale( v, ", "oak_double( ", "oak_length( s )"} {
		if !strings.Contains(out, want) {
			t.Fatalf("emitted C lacks %q", want)
		}
	}
}

// Across packages, recv.f(args) reaches an exported function f of the
// package that declares recv's type without naming the alias, and never an
// unexported one; a field is never callable this way; an unknown name is
// an error that names the receiver type.
func TestE2EUniformCallAcrossPackages(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/ufcs\noak 0.1.0\n",
		"geo/geo.oak": `package geo
pub Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
pub shift: (p: Point, dx: i32): Point = Point { x: p.x + dx, y: p.y }
pub sum: (p: Point): i32 = p.x + p.y
hidden: (p: Point): i32 = 0
`,
		"main.oak": `package main
import("example.com/ufcs/geo")
main: (): i32 {
  p: geo.Point = geo.make(1, 2)
  p.shift(39).sum()
}
`,
	})
	_, code, abnormal := buildAndRunFrom(t, "ufcs", New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	rejected := writeModule(t, map[string]string{
		"oak.mod": "module example.com/ufcs2\noak 0.1.0\n",
		"geo/geo.oak": `package geo
pub Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
hidden: (p: Point): i32 = 0
`,
		"main.oak": `package main
import("example.com/ufcs2/geo")
main: (): i32 { geo.make(1, 2).hidden() }
`,
	})
	_, err := New().WithPackageDir(rejected).Check().Get()
	if err == nil || !strings.Contains(err.Error(), "no method or function hidden") {
		t.Fatalf("unexported function reachable through uniform call syntax: %v", err)
	}
	cases := []struct{ name, src, want string }{
		{"field", "Vec: type = struct { x: f32, y: f32 }\nmain: (): i32 {\n  v: Vec = Vec { x: 1.0, y: 2.0 }\n  v.x()\n  0\n}", "x is a field of Vec, not a function"},
		{"unknown", "Vec: type = struct { x: f32, y: f32 }\nmain: (): i32 {\n  v: Vec = Vec { x: 1.0, y: 2.0 }\n  v.norm()\n  0\n}", "no method or function norm for Vec"},
		{"arity", "Vec: type = struct { x: f32, y: f32 }\nscale: (v: Vec, k: f32): Vec = v\nmain: (): i32 {\n  v: Vec = Vec { x: 1.0, y: 2.0 }\n  w: Vec = v.scale()\n  0\n}", "argument"},
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

// A method declared for an ADT receiver wins over a free function of the
// same name: with both declared, s.size() has the method's type.
func TestUniformCallMethodPrecedence(t *testing.T) {
	src := `
Shape: type = Dot | Line: u32
fn (s: Shape) size(): u32 = s ? | .Dot => u32(1) | .Line(n) => n
size: (s: Shape): Bool = true
main: (): i32 {
  s: Shape = .Line(u32(5))
  n: u32 = s.size()
  i32_bits_u32(n)
}
`
	if _, err := New().WithSource("precedence.oak", src).Check().Get(); err != nil {
		t.Fatalf("the method should win: %v", err)
	}
	// Without the method, the same call is the free function and the u32
	// binding is a type error.
	free := `
Shape: type = Dot | Line: u32
size: (s: Shape): Bool = true
main: (): i32 {
  s: Shape = .Line(u32(5))
  n: u32 = s.size()
  i32_bits_u32(n)
}
`
	if _, err := New().WithSource("free.oak", free).Check().Get(); err == nil {
		t.Fatalf("a Bool result bound to u32 should be rejected")
	}
}
