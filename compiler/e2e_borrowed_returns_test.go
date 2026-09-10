package compiler

import (
	"strings"
	"testing"
)

// Region-indexed borrowed returns, increment 1 (docs/spec/50-borrowing.md
// section 8c): a function with a `[]T` return and one `[]T` parameter hands
// back a view of that parameter's owner — a frame cursor a decoder can
// return — and the caller's binding is a reborrow of the argument. Executed
// in both realizations; the C is the `{base, len}` view struct returned by
// value.
const borrowedReturnsProgram = `
frame: (buf: []u8, at: u32): []u8 = subslice(buf, at, 2)
head: (buf: []u8, n: u32): []u8 = buf[0:n]
pick: (buf: []u8, first: Bool): []u8 = first ? { subslice(buf, 0, 1) } | { subslice(buf, 3, 1) }
sum: (v: []u8): u32 {
  total: u32 = 0
  i: u32 = 0
  while i < len(v) {
    total = total + u32(v[i])
    i = i + 1
  }
  total
}
main: (): i32 {
  data: [4]u8 = [4]u8{ 10, 20, 30, 40 }
  v: []u8 = view(&data)
  f: []u8 = frame(v, 1)
  assert(len(f) == 2 && f[0] == 20 && f[1] == 30)
  g: []u8 = head(frame(v, 1), 1)
  assert(len(g) == 1 && g[0] == 20)
  h: []u8 = head(view(&data), 3)
  assert(sum(h) == 60)
  p: []u8 = pick(v, false)
  assert(p[0] == 40)
  assert(sum(frame(v, 2)) == 70)
  i32_bits_u32(sum(f) + sum(g)) - 28
}
`

func TestE2EBorrowedReturns(t *testing.T) {
	output, err := New().WithSource("frames.oak", borrowedReturnsProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_view_u8 oak_frame( oak_view_u8 buf, u32 at )"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "frames", borrowedReturnsProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, borrowedReturnsProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// What the rule refuses: a returned view of a local owner (OAK-B0113), a
// signature with two candidate parameters or an owned-array parameter
// (OAK-B0109, the conservative rule), and a caller writing the owner while
// the returned view lives (OAK-B0103).
func TestBorrowedReturnsRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"local owner", `
dangle: (buf: []u8): []u8 {
  local: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  view(&local)
}
main: (): i32 { 0 }`, "OAK-B0113"},
		{"other parameter's owner", `
wrong: (buf: []u8, n: u32): []u8 {
  local: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  subslice(view(&local), 0, n)
}
main: (): i32 { 0 }`, "OAK-B0113"},
		{"two candidates", `
split: (a: []u8, b: []u8): []u8 = a
main: (): i32 { 0 }`, "OAK-B0109"},
		{"owned array parameter", `
dangle: (buf: [4]u8): []u8 = buf[0:2]
main: (): i32 { 0 }`, "OAK-B0109"},
		{"owner written while result lives", `
frame: (buf: []u8, at: u32): []u8 = subslice(buf, at, 2)
main: (): i32 {
  data: [4]u8 = [4]u8{ 1, 2, 3, 4 }
  v: []u8 = view(&data)
  f: []u8 = frame(v, 1)
  data[0] = 9
  i32(f[0])
}`, "OAK-B0103"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
}
