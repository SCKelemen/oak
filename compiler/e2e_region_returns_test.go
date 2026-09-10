package compiler

import (
	"strings"
	"testing"
)

// Region-indexed borrowed returns, increments 2 and 3
// (docs/spec/50-borrowing.md section 8c): explicit region parameters
// erased before checking, span returns as reborrows, and a record carrying
// a region — a cursor — opened, advanced, and read through calls. Regions
// are phantom: the C is the same {base, len} structs by value.
const regionReturnsProgram = `
Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
open[R]: (buf: View[u8, R]): Cursor[R] = Cursor { data: buf, pos: 0 }
advance[R]: (c: Cursor[R], n: u32): Cursor[R] = Cursor { data: c.data, pos: c.pos + n }
current[R]: (c: Cursor[R]): View[u8, R] = subslice(c.data, c.pos, 1)
pick[R]: (a: View[u8, R], b: []u8, first: Bool): View[u8, R] = first ? { subslice(a, 0, 1) } | { subslice(a, 1, 1) }
tail[R]: (buf: Span[u8, R], from: u32): Span[u8, R] = subslice(buf, from, 2)
fill: (s: [*]u8, value: u8): () {
  i: u32 = 0
  while i < len(s) {
    s[i] = value
    i = i + 1
  }
}
write_tail: (s: [*]u8): () {
  t: [*]u8 = tail(s, 2)
  fill(t, 7)
}
main: (): i32 {
  data: [4]u8 = [4]u8{ 10, 20, 30, 40 }
  other: [2]u8 = [2]u8{ 1, 2 }
  v: []u8 = view(&data)
  c: Cursor = open(v)
  d: Cursor = advance(c, 2)
  cur: []u8 = current(d)
  assert(cur[0] == 30 && d.pos == 2 && c.pos == 0)
  e: Cursor = advance(advance(c, 1), 2)
  assert(current(e)[0] == 40)
  p: []u8 = pick(v, view(&other), false)
  assert(p[0] == 20)
  scratch: [4]u8 = [4]u8{ 0, 0, 0, 0 }
  write_tail(span(&scratch))
  assert(scratch[0] == 0 && scratch[1] == 0 && scratch[2] == 7 && scratch[3] == 7)
  i32_bits_u32(u32(cur[0]) + u32(scratch[3]) + u32(p[0]) - 15)
}
`

func TestE2ERegionReturns(t *testing.T) {
	output, err := New().WithSource("regions.oak", regionReturnsProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"oak_Cursor oak_open( oak_view_u8 buf )",
		"oak_view_u8 oak_current( oak_Cursor c )",
		"oak_span_u8 oak_tail( oak_span_u8 buf, u32 from )",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "regions", regionReturnsProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, regionReturnsProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

func TestRegionReturnsRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"record of a local", `
Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
bad[R]: (buf: View[u8, R]): Cursor[R] {
  local: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  Cursor { data: view(&local), pos: 0 }
}
main: (): i32 { 0 }`, "OAK-B0113"},
		{"region names two parameters", `
both[R]: (a: View[u8, R], b: View[u8, R]): View[u8, R] = a
main: (): i32 { 0 }`, "OAK-B0113"},
		{"owner written while cursor lives", `
Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
open[R]: (buf: View[u8, R]): Cursor[R] = Cursor { data: buf, pos: 0 }
main: (): i32 {
  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  c: Cursor = open(view(&data))
  data[0] = 9
  i32(c.data[0])
}`, "OAK-B0103"},
		{"parent span used while returned span lives", `
tail[R]: (buf: Span[u8, R], from: u32): Span[u8, R] = subslice(buf, from, 1)
main: (): i32 {
  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  s: [*]u8 = span(&data)
  t: [*]u8 = tail(s, 1)
  s[0] = 9
  i32(t[0])
}`, "OAK-B0107"},
		{"record parameter without a region", `
Cursor: type = struct { data: []u8, pos: u32 }
peek: (c: Cursor): u8 = c.data[0]
main: (): i32 { 0 }`, "OAK-B0109"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
}
