package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Nested records and array fields through the native backend
// (docs/spec/94-assembler.md §9, eighth increment): a record field that is
// itself a declared record or an owned array is placed by the same natural
// layout the C backend asserts; access chains resolve to frame places —
// scalar fields load and store at their offset, nested records copy by
// their exact size, array fields go through the owned-array idiom. The C
// backend's realization of the same program is the oracle.
const nativeNestedProgram = `
Point: type = struct {
  x: i32
  y: i32
}

Rect: type = struct {
  a: Point
  b: Point
  tag: u8
}

Hist: type = struct {
  name: u8
  counts: [4]u32
  total: u32
}

shift: (p: Point, dx: i32) -> Point = Point { x: p.x + dx, y: p.y }

// The corpus shape: nested records built from locals and a call's result.
corner_sum: () -> i32 {
  p: Point = Point { x: 11, y: 31 }
  q: Point = shift(p, 9)
  r: Rect = Rect { a: p, b: q, tag: u8(3) }
  assert(r.b.x == 20)
  r.a.x + r.b.y + i32(r.tag)
}

// Nested field stores, a nested record passed on and copied out.
widen: (r: Rect, d: i32) -> Rect {
  r.a.x = r.a.x - d
  r.b = shift(r.b, d)
  r
}

// An array field walked by a loop index and by literal indices.
bucket: (v: []u8) -> u32 {
  h: Hist = Hist { name: u8(1), counts: [u32(0), u32(0), u32(0), u32(0)], total: u32(0) }
  i: u32 = u32(0)
  while i < len(v) {
    b: u32 = u32(v[i]) >> u32(6)
    h.counts[b] = h.counts[b] + u32(1)
    h.total = h.total + u32(1)
    i = i + u32(1)
  }
  h.counts[0] * u32(1000) + h.counts[1] * u32(100) + h.counts[2] * u32(10) + h.counts[3] + h.total * u32(10000) + u32(len(h.counts)) * u32(100000)
}

// A nested record at a 4-byte offset handed to a call (aligned through a
// copy) and a whole nested record read back into a local.
inner: (r: Rect) -> i32 {
  c: Point = r.b
  c.y = c.y + 1
  shift(r.a, 1).x + c.y
}

main: (): i32 {
  assert(corner_sum() == 45)
  r: Rect = Rect { a: Point { x: 5, y: 6 }, b: Point { x: 7, y: 8 }, tag: u8(9) }
  w: Rect = widen(r, 2)
  assert(w.a.x == 3)
  assert(w.b.x == 9)
  assert(w.b.y == 8)
  assert(r.a.x == 5)
  assert(w.tag == u8(9))
  data: [8]u8
  data[0] = u8(10)
  data[1] = u8(70)
  data[2] = u8(130)
  data[3] = u8(200)
  data[4] = u8(255)
  data[7] = u8(64)
  assert(bucket(view(&data)) == u32(483212))
  assert(inner(r) == 15)
  42
}
`

func TestE2ENativeNestedRecords(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("nested.oak", nativeNestedProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_nested", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native nested records: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"shift", "corner_sum", "widen", "bucket", "inner", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_nested_c", New().WithSource("nested.oak", nativeNestedProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_nested_portable", New().WithSource("nested.oak", nativeNestedProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
