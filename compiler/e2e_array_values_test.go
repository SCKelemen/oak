package compiler

import (
	"strings"
	"testing"
)

// Owned arrays are values at a function boundary (ml finding F15): a store
// through an array parameter never reaches the caller, in both realizations,
// and a typed array literal is an ordinary argument. The C representation is
// a wrapper struct carrying the array (docs/spec/90-backend.md section 10),
// so the parameter copy is C's own by-value passing: no copy-in prologue.
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
	for _, want := range []string{
		"typedef struct oak_arr_u32_4 { u32 v[ 4 ]; } oak_arr_u32_4;",
		"oak_poke( oak_arr_u32_4 d )",
		"oak_total( (oak_arr_u32_4){ { 40, 2, 0, 0 } } )",
		"oak_arr_u32_4 d = { { 1, 2, 3, 36 } };",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	for _, stale := range []string{"oak_in_", "oak_k", "u32[4]", "[ 4 ] d", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, stale) {
			t.Fatalf("generated C still carries the raw-array shape %q:\n%s", stale, output)
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

// The wrapper representation makes every array position a value position:
// an array is returned by value, copied into a record field from a binding,
// assigned whole, read back out of a record field, sliced in argument
// position, and rebound through a tail-recursive call — with no aliasing
// anywhere. The interpreter agrees.
func TestE2EArraysAreValuesEverywhere(t *testing.T) {
	src := `
Shape: type = struct { rank: u32, dims: [4]u32 }
make: (): [4]u32 {
  [4]u32{ 1, 2, 3, 36 }
}
wrap: (d: [4]u32): Shape {
  Shape { rank: 1, dims: d }
}
total: (d: [4]u32): u32 {
  d[0] + d[1] + d[2] + d[3]
}
first_two: (v: []u32): u32 {
  v[0] + v[1]
}
fill: (d: [4]u32, i: u32): [4]u32 {
  i >= 4 ? { d } | {
    d[i] = i * 10
    fill(d, i + 1)
  }
}
main: (): i32 {
  a: [4]u32 = make()
  b: [4]u32 = a
  b[0] = 100
  assert(a[0] == 1)
  assert(total(b) == 141)
  s: Shape = wrap(a)
  a[1] = 7
  assert(s.dims[1] == 2)
  assert(total(s.dims) == 42)
  c: [4]u32 = b
  c = s.dims
  c[2] = 5
  assert(total(c) == 44)
  assert(s.dims[2] == 3)
  assert(first_two(a[0:2]) == 8)
  f: [4]u32 = fill(a, 0)
  assert(f[3] == 30)
  assert(a[3] == 36)
  42
}
`
	output, err := New().WithSource("arrayseverywhere.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"oak_arr_u32_4 oak_make( void )",
		"oak_arr_u32_4 oak_fill( oak_arr_u32_4 d, u32 i )",
		"= s.dims",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "arrayseverywhere", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// A packed record with an array member keeps its dense layout: the wrapper
// struct has the array's own size and alignment, and cc ratifies the
// emitted offsetof and sizeof assertions.
func TestE2EPackedRecordWithArrayField(t *testing.T) {
	src := `
Packet: type = struct(packed) {
  tag: u8
  body: [3]u8
  crc: u16
}
main: (): i32 {
  p: Packet = Packet { tag: 1, body: [3]u8{ 10, 20, 12 }, crc: 8 }
  p.body[1] = 11
  assert(size_of[Packet]() == 6)
  assert(offset_of[Packet](crc) == 4)
  u32(p.body[0]) + u32(p.body[1]) + u32(p.body[2]) + u32(p.tag) + u32(p.crc) == 42 ? { 42 } | { 1 }
}
`
	code, abnormal := buildAndRun(t, "packedarray", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// An owned-array payload of a tagged union is a value too: the variant
// constructor takes and stores the wrapper struct.
func TestE2EArrayVariantPayload(t *testing.T) {
	src := `
Box: type = Empty | Value: [4]u8
weight: (b: Box): u32 = b ?
  | .Value(d) => u32(d[0]) + u32(d[1]) + u32(d[2]) + u32(d[3])
  | .Empty => u32(0)
main: (): i32 {
  d: [4]u8 = [4]u8{ 40, 2, 0, 0 }
  b: Box = .Value(d)
  e: Box = .Empty
  d[0] = 1
  weight(b) == 42 && weight(e) == 0 ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("arraypayload.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "arraypayload", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}
