package compiler

import (
	"strings"
	"testing"
)

// Scalar views of record views (docs/spec/50-borrowing.md section 8d, the
// ml pilot's F6): view_as[U](rows) is the same storage as a []U when every
// field of the record is U or a fixed array of U, and tensor_strided lays a
// field across positions out as a tensor without a copy.

const scalarViewProgram = `package main

t := import("tensor")

Row: type = struct { q: [2]f32, k: [2]f32, v: [2]f32 }

main: (): i32 = {
  cache: [3]Row = [
    Row { q: [1.0, 2.0], k: [3.0, 4.0], v: [5.0, 6.0] },
    Row { q: [7.0, 8.0], k: [9.0, 10.0], v: [11.0, 12.0] },
    Row { q: [13.0, 14.0], k: [15.0, 16.0], v: [17.0, 18.0] }
  ]
  flat: []f32 = view_as[f32](view(&cache))
  ks: t.Tensor2 = t.tensor_strided(flat, 3, 2, 6, 1, 2)
  len(flat) != 18 ? 10 | flat[0] != 1.0 ? 11 | flat[17] != 18.0 ? 12 |
  t.tensor_at(ks, 0, 0) != 3.0 ? 13 | t.tensor_at(ks, 1, 1) != 10.0 ? 14 | t.tensor_at(ks, 2, 0) != 15.0 ? 15 |
  t.tensor_sum(ks) != 57.0 ? 16 | 42
}
`

func TestE2EScalarViewOfRecords(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": scalarViewProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "(oak_view_f32){ (const f32 *)( (oak_view_oak_Row){ cache.v, 3 } ).base, (u32)(( (oak_view_oak_Row){ cache.v, 3 } ).len * 6u) }") {
		t.Fatalf("the scalar view must be the source's storage with the record's scalar count:\n%s", emitted)
	}
}

// The interpreter reads the same scalars in declaration order, fixed-array
// fields spliced; the extraction is the flatMap of the fields.
func TestScalarViewInterpretedAndExtracted(t *testing.T) {
	src := `
Pair: type = struct { lo: u32, hi: [2]u32 }
total: (v: []u32): u32 = {
  acc: u32 = 0
  i: u32 = 0
  n: u32 = len(v)
  while i < n {
    acc = acc + v[i] * (i + 1)
    i = i + 1
  }
  acc
}
main: (): i32 = {
  pairs: [2]Pair = [Pair { lo: 1, hi: [2, 3] }, Pair { lo: 4, hi: [5, 6] }]
  flat: []u32 = view_as[u32](view(&pairs))
  i32_bits_u32(total(flat) - 49)
}
`
	// 1*1 + 2*2 + 3*3 + 4*4 + 5*5 + 6*6 = 91; 91 - 49 = 42.
	if got := interpret(t, src); got != 42 {
		t.Fatalf("interpreter = %d, want 42", got)
	}
	code, abnormal := buildAndRun(t, "scalar_view_pairs", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	extracted, err := New().WithSource("scalar_view.oak", src).EmitLean("Oak.ScalarView").Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(extracted, ".toList.flatMap (fun r => ([] : List UInt32) ++ [r.lo] ++ r.hi.toList)).toArray)") {
		t.Fatalf("view_as must extract as the flatMap of the fields:\n%s", extracted)
	}
}

// The rule fails closed: a field of another type, a non-record source, a
// span source, a missing target type, and a target that is not a scalar.
func TestScalarViewRejections(t *testing.T) {
	cases := map[string][2]string{
		"mixed fields": {`Mixed: type = struct { a: f32, n: u32 }
main: (): i32 = {
  xs: [1]Mixed = [Mixed { a: 1.0, n: 2 }]
  flat: []f32 = view_as[f32](view(&xs))
  i32(len(flat))
}`, "field n of Mixed is u32"},
		"non-record": {`main: (): i32 = {
  xs: [4]u32 = [1, 2, 3, 4]
  flat: []u8 = view_as[u8](view(&xs))
  i32(len(flat))
}`, "reinterprets a view of records"},
		"span source": {`Row: type = struct { a: f32 }
main: (): i32 = {
  xs: [1]Row = [Row { a: 1.0 }]
  flat: []f32 = view_as[f32](span(&xs))
  i32(len(flat))
}`, "view_as takes a read-only view"},
		"missing target": {`Row: type = struct { a: f32 }
main: (): i32 = {
  xs: [1]Row = [Row { a: 1.0 }]
  flat: []f32 = view_as(view(&xs))
  i32(len(flat))
}`, "takes its target type"},
		"record target": {`Row: type = struct { a: f32 }
main: (): i32 = {
  xs: [1]Row = [Row { a: 1.0 }]
  flat: []Row = view_as[Row](view(&xs))
  i32(len(flat))
}`, "the target is a fixed-width integer or floating-point type"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c[0]).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: compiled; want %q", name, c[1])
		}
		if !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %q, got %v", name, c[1], err)
		}
	}
}
