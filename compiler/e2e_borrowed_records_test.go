package compiler

import (
	"strings"
	"testing"
)

// Borrows inside aggregates (docs/spec/50-borrowing.md): a local record may
// hold views of owners in scope — a cursor over a buffer — and is then a
// borrow of those owners itself: the owner stays readable and unwritable
// while the record lives, the record's view fields index with their bounds
// check, a copy of the record reproduces the borrows, and the record's
// layout is proven like any other.
func TestE2ERecordHoldingViews(t *testing.T) {
	src := `
Cursor: type = struct { data: []u8, pos: u32 }
sum_from: (src: []u8): u32 {
  c: Cursor = Cursor { data: src, pos: 0 }
  total: u32 = 0
  while c.pos < len(c.data) {
    total = total + u32(c.data[c.pos])
    c.pos = c.pos + 1
  }
  total
}
main: (): i32 {
  buf: [4]u8 = [4]u8{ 10, 20, 12, 0 }
  c: Cursor = Cursor { data: view(&buf), pos: 1 }
  d: Cursor = c
  assert(len(c.data) == 4)
  assert(c.data[0] == 10)
  assert(d.data[2] == 12)
  assert(sum_from(view(&buf)) == 42)
  sum_from(c.data) == 42 ? { 42 } | { 1 }
}
`
	output, err := New().WithSource("cursor.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"  oak_view_u8 data;", "oak_view_index_u8( c.data, (u64)( 0 ) )"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "cursor", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, src); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
	// The view field is the {base, len} struct at its natural placement; the
	// layout builtins are compiled-backend facts, so this program is not
	// interpreted.
	layout := `
Cursor: type = struct { data: []u8, pos: u32 }
main: (): i32 {
  assert(offset_of[Cursor](pos) == 16)
  assert(size_of[Cursor]() == 24)
  assert(align_of[Cursor]() == 8)
  42
}
`
	code, abnormal = buildAndRun(t, "cursorlayout", layout)
	if abnormal || code != 42 {
		t.Fatalf("layout exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// The record is a borrow: writing the owner while it lives, returning it,
// storing it, passing it, or reassigning its view field is rejected, and a
// view of a temporary or unknown source cannot be captured at all.
func TestRecordHoldingViewsRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"owner-written", `
Cursor: type = struct { data: []u8, pos: u32 }
main: (): i32 {
  buf: [4]u8
  c: Cursor = Cursor { data: view(&buf), pos: 0 }
  buf[0] = 1
  i32_bits_u32(c.pos)
}`, "cannot be written while read-only views are active"},
		{"returned", `
Cursor: type = struct { data: []u8, pos: u32 }
open: (src: []u8): Cursor = Cursor { data: src, pos: 0 }
main: (): i32 { 0 }`, "OAK-B0109"},
		{"passed", `
Cursor: type = struct { data: []u8, pos: u32 }
sink: (c: Cursor): u32 = c.pos
main: (): i32 {
  buf: [4]u8
  c: Cursor = Cursor { data: view(&buf), pos: 0 }
  i32_bits_u32(sink(c))
}`, "OAK-B0109"},
		{"field-reassigned", `
Cursor: type = struct { data: []u8, pos: u32 }
main: (): i32 {
  buf: [4]u8
  other: [4]u8
  c: Cursor = Cursor { data: view(&buf), pos: 0 }
  c.data = view(&other)
  i32_bits_u32(c.pos)
}`, "OAK-B0109"},
		{"unknown-source", `
Cursor: type = struct { data: []u8, pos: u32 }
main: (): i32 {
  c: Cursor = Cursor { data: str_bytes("abc"), pos: 0 }
  i32_bits_u32(c.pos)
}`, "OAK-B0109"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Fatalf("%s: want %q, got %v", c.name, c.want, err)
			}
		})
	}
}
