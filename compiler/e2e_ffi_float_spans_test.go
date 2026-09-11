package compiler

import (
	"encoding/binary"
	"math"
	"testing"
)

// Boundary spans over floating-point elements and over declared structs
// with proven layouts (docs/spec/92-ffi.md section 2.5.1): the pointer and
// element count reach C unchanged. libc write takes a byte count, so a
// view of exactly eight f64 (or eight 8-byte Points) starting at element i
// makes write emit the eight bytes of element i: every element of the view
// and every field of every struct is checked at the offset the backend
// asserted.
func TestE2EBoundarySpanFloatAndStructElements(t *testing.T) {
	stdout, code, abnormal := buildAndRunOutput(t, "ffifloatspans", `
Point: type = struct { x: f32, y: f32 }

write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")

dump_f64: (xs: []f64): () {
  _ = write(c.Int(1), c.span_of(xs))
}

dump_points: (ps: []Point): () {
  _ = write(c.Int(1), c.span_of(ps))
}

main: (): i32 {
  values: [10]f64 = [10]f64{1.5, -0.1, 1e300, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0}
  all: []f64 = view(&values)
  dump_f64(all[0:8])
  dump_f64(all[1:9])
  dump_f64(all[2:10])
  origin: Point = Point { x: 0.0, y: 0.0 }
  points: [9]Point = [9]Point{Point { x: 1.0, y: 2.0 }, Point { x: -3.5, y: 0.25 }, origin, origin, origin, origin, origin, origin, origin}
  ps: []Point = view(&points)
  dump_points(ps[0:8])
  dump_points(ps[1:9])
  0
}
`)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
	raw := []byte(stdout)
	if len(raw) != 3*8+2*8 {
		t.Fatalf("stdout carries %d bytes, want %d", len(raw), 3*8+2*8)
	}
	for i, want := range []float64{1.5, -0.1, 1e300} {
		got := math.Float64frombits(binary.LittleEndian.Uint64(raw[i*8:]))
		if got != want {
			t.Errorf("f64 element %d = %v, want %v", i, got, want)
		}
	}
	for i, want := range [][2]float32{{1.0, 2.0}, {-3.5, 0.25}} {
		base := 24 + i*8
		x := math.Float32frombits(binary.LittleEndian.Uint32(raw[base:]))
		y := math.Float32frombits(binary.LittleEndian.Uint32(raw[base+4:]))
		if x != want[0] || y != want[1] {
			t.Errorf("point %d = (%v, %v), want (%v, %v)", i, x, y, want[0], want[1])
		}
	}
}
