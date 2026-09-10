package compiler

import (
	"strings"
	"testing"
)

// Owned arrays are values at a function boundary (ml finding F15): a store
// through an array parameter never reaches the caller, in both realizations,
// and a typed array literal is an ordinary argument.
func TestE2EArrayParametersAreValues(t *testing.T) {
	src := `
poke: (d: [4]u32): u32 {
  d[0] = 99
  d[0]
}
total: (d: [4]u32): u32 {
  d[0] + d[1] + d[2] + d[3]
}
main: (): i32 {
  d: [4]u32 = [4]u32{ 1, 2, 3, 36 }
  assert(poke(d) == 99)
  assert(d[0] == 1)
  assert(total(d) == 42)
  assert(total([4]u32{ 40, 2, 0, 0 }) == 42)
  d[0] == 1 ? { 42 } | { 7 }
}
`
	output, err := New().WithSource("arrayvalues.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"const u32 oak_in_d[4]", "d[oak_k] = oak_in_d[oak_k]", "oak_total( (u32[4]){ 40, 2, 0, 0 } )"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	code, abnormal := buildAndRun(t, "arrayvalues", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// A shape travels as one record holding its extents, constructed from an
// array literal and passed or returned by value.
func TestE2EShapeRecordCarriesItsExtents(t *testing.T) {
	src := `
Shape: type = struct { rank: u32, dims: [4]u32 }
reshape: (r: u32, c: u32): Shape {
  Shape { rank: 2, dims: [4]u32{ r, c, 0, 0 } }
}
volume: (s: Shape): u32 {
  s.dims[0] * s.dims[1]
}
main: (): i32 {
  s: Shape = reshape(3, 4)
  volume(s) == 12 && s.rank == 2 ? { 42 } | { 1 }
}
`
	code, abnormal := buildAndRun(t, "shape", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// The two array shapes that have no C lowering yet are rejected with a
// pointer at the record wrapper instead of being emitted as invalid C.
func TestArrayValueGapsAreDiagnosed(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"array-return", "make: (): [4]u32 {\n  [4]u32{ 1, 2, 3, 4 }\n}\nmain: (): i32 { 0 }", "returning an owned array by value is not lowered yet; return it inside a record"},
		{"array-field-copy", "Shape: type = struct { dims: [4]u32 }\nwrap: (d: [4]u32): Shape {\n  Shape { dims: d }\n}\nmain: (): i32 { 0 }", "an owned array field must be initialized from an array literal"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
}
