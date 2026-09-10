package compiler

import (
	"strings"
	"testing"
)

// Operator definitions (docs/spec/10-syntax.md section 14, ml ask 5.3): an
// `operator(SYM)` marker binds SYM for a left operand of the function's
// first parameter type, and `a SYM b` is then exactly the call. Arithmetic
// and comparison symbols, a literal right operand taking the parameter's
// type, chaining through ordinary precedence, and an ADT left operand all
// lower to plain calls; compiled and interpreted results agree.
func TestE2EOperatorDefinitions(t *testing.T) {
	src := `
Vec: type = struct { x: f32, y: f32 }
operator(+) add: (a: Vec, b: Vec): Vec = Vec { x: a.x + b.x, y: a.y + b.y }
operator(-) sub: (a: Vec, b: Vec): Vec = Vec { x: a.x - b.x, y: a.y - b.y }
operator(*) scale: (v: Vec, k: f32): Vec = Vec { x: v.x * k, y: v.y * k }
operator(==) same: (a: Vec, b: Vec): Bool = a.x == b.x && a.y == b.y
operator(<) shorter: (a: Vec, b: Vec): Bool = a.x * a.x + a.y * a.y < b.x * b.x + b.y * b.y

Money: type = Cents: u32 | Free
operator(+) plus: (a: Money, b: Money): Money = a ? | .Free => b | .Cents(x) => (b ? | .Free => a | .Cents(y) => .Cents(x + y))
cents: (m: Money): u32 = m ? | .Free => u32(0) | .Cents(c) => c

main: (): i32 {
  a: Vec = Vec { x: 1.0, y: 2.0 }
  b: Vec = Vec { x: 3.0, y: 4.0 }
  c: Vec = a + b * 2.0                       // add(a, scale(b, 2.0)) = (7, 10)
  d: Vec = c - a                             // (6, 8)
  ok1: Bool = d == Vec { x: 6.0, y: 8.0 }
  ok2: Bool = a < b && !(b < a)
  total: Money = .Cents(u32(40)) + .Free + .Cents(u32(2))
  ok1 && ok2 && cents(total) == u32(42) ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "operators", src)
	if abnormal || code != 42 {
		t.Fatalf("compiled exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter main() = %d, want 42", got)
	}
	out, err := New().WithSource("operators.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_add( a, oak_scale( b, ", "oak_sub( c, a )", "oak_same( d, "} {
		if !strings.Contains(out, want) {
			t.Fatalf("emitted C lacks %q", want)
		}
	}
}

// Across packages the binding travels with the type: main uses `+` on a
// geo.Point without naming geo.add. Declaring an operator for a type
// outside the type's package, binding a symbol twice, binding a primitive
// left type, a comparison that is not Bool, and a non-bindable symbol are
// rejected; an unbound symbol on a declared type keeps its error.
func TestOperatorDefinitionRules(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/ops\noak 0.1.0\n",
		"geo/geo.oak": `package geo
pub Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
pub sum: (p: Point): i32 = p.x + p.y
pub operator(+) add: (a: Point, b: Point): Point = Point { x: a.x + b.x, y: a.y + b.y }
`,
		"main.oak": `package main
import("example.com/ops/geo")
main: (): i32 {
  p: geo.Point = geo.make(1, 2) + geo.make(3, 4) + geo.make(30, 2)
  geo.sum(p)
}
`,
	})
	_, code, abnormal := buildAndRunFrom(t, "ops", New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	foreign := writeModule(t, map[string]string{
		"oak.mod": "module example.com/ops2\noak 0.1.0\n",
		"geo/geo.oak": `package geo
pub Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
`,
		"main.oak": `package main
import("example.com/ops2/geo")
operator(+) add: (a: geo.Point, b: geo.Point): geo.Point = geo.make(a.x + b.x, a.y + b.y)
main: (): i32 { 0 }
`,
	})
	if _, err := New().WithPackageDir(foreign).Check().Get(); err == nil || !strings.Contains(err.Error(), "must be declared in the package that declares") {
		t.Fatalf("operator for an imported type accepted outside its package: %v", err)
	}
	cases := []struct{ name, src, want string }{
		{"duplicate", "Vec: type = struct { x: f32 }\noperator(+) add: (a: Vec, b: Vec): Vec = a\noperator(+) plus: (a: Vec, b: Vec): Vec = b\nmain: (): i32 { 0 }", "already bound for Vec by add"},
		{"primitive", "operator(+) add: (a: u32, b: u32): u32 = a\nmain: (): i32 { 0 }", "must be a declared record or ADT type"},
		{"comparison-type", "Vec: type = struct { x: f32 }\noperator(==) same: (a: Vec, b: Vec): u32 = u32(0)\nmain: (): i32 { 0 }", "must return Bool"},
		{"arity", "Vec: type = struct { x: f32 }\noperator(+) add: (a: Vec): Vec = a\nmain: (): i32 { 0 }", "exactly two parameters"},
		{"symbol", "Vec: type = struct { x: f32 }\noperator(&&) both: (a: Vec, b: Vec): Vec = a\nmain: (): i32 { 0 }", "can be bound"},
		{"unbound", "Vec: type = struct { x: f32 }\noperator(+) add: (a: Vec, b: Vec): Vec = a\nmain: (): i32 {\n  v: Vec = Vec { x: 1.0 }\n  w: Vec = v * v\n  0\n}", "operator *"},
		{"right-operand", "Vec: type = struct { x: f32 }\noperator(*) scale: (v: Vec, k: f32): Vec = v\nmain: (): i32 {\n  v: Vec = Vec { x: 1.0 }\n  w: Vec = v * v\n  0\n}", "right operand Vec does not match f32"},
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
