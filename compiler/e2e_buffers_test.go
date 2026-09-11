package compiler

import (
	"strings"
	"testing"
)

// Owned foreign buffers (docs/spec/92-ffi.md section 2.8) with the arena
// package: a program takes ownership of a libc allocation as a
// Buffer[f32], reserves ranges from an arena over its element space,
// fills one range through a span, reads it back through a view and a
// Tensor region record, hands the memory back with c.disown, and frees
// it. Every view and span is bounds-checked against the count the buffer
// was created with; the interpreter has no foreign memory, so this runs
// compiled only.
const bufferProgram = `import("arena")

malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")

Tensor[R]: type = struct { data: View[f32, R], rows: u32, cols: u32 }
tensor_of[R]: (data: View[f32, R], rows: u32, cols: u32): Tensor[R] = Tensor { data: data, rows: rows, cols: cols }
sum[R]: (t: Tensor[R]): f32 {
  total: f32 = 0.0
  i: u32 = 0
  while i < len(t.data) {
    total = total + t.data[i]
    i = i + u32(1)
  }
  total
}

fill: (s: [*]f32, offset: u32, count: u32, base: f32): () {
  part: [*]f32 = subslice(s, offset, count)
  i: u32 = 0
  while i < len(part) {
    part[i] = base + f32_round_u32(i)
    i = i + u32(1)
  }
}

tensor_sum: (v: []f32, offset: u32): f32 {
  t: Tensor = tensor_of(subslice(v, offset, u32(6)), u32(2), u32(3))
  sum(t)
}

main: (): i32 {
  count: u32 = u32(4096)
  p: c.Ptr = malloc(c.Size(count * u32(4)))
  ok: Bool = false
  unsafe {
    weights: Buffer[f32] = c.own[f32](p, count)
    a: arena.Arena = arena.arena_new(len(weights))
    r1: arena.Reservation = arena.arena_reserve(a, u32(6), u32(16))
    r2: arena.Reservation = arena.arena_reserve(r1.arena, u32(1000), u32(16))
    r3: arena.Reservation = arena.arena_reserve(r2.arena, u32(5000), u32(1))
    fill(span(&weights), r1.offset, u32(6), 1.0)
    fill(span(&weights), r2.offset, u32(1000), 0.0)
    total: f32 = tensor_sum(view(&weights), r1.offset)
    ok = r1.ok && r2.ok && !r3.ok && r1.offset == u32(0) && r2.offset == u32(16) && total == 21.0
    ok = ok && len(weights) == count && arena.arena_remaining(r2.arena) == count - u32(1016) && r3.arena.used == r2.arena.used
    q: c.Ptr = c.disown(weights)
    free(q)
  }
  ok ? 42 | 1
}
`

func TestE2EOwnedBuffers(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/buffers\noak 0.1.0\n",
		"main.oak": "package main\n" + bufferProgram,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("compiled buffer program exited (%d, abnormal=%v)", code, abnormal)
	}
}

// A Buffer is an owner, never a value, and it ends with c.disown: every
// other use fails closed (a generic instantiation over it is refused by
// the mangling rule before the argument rule can name it).
func TestOwnedBufferRejections(t *testing.T) {
	prelude := "malloc: (n: c.Size): c.Ptr = c.extern(\"malloc\")\n"
	cases := map[string]struct{ src, want string }{
		"outside unsafe": {prelude + `
f: (): u32 {
  b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
  len(b)
}
main: (): i32 = 0
`, "OAK-F0107"},
		"copy": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
    b2: Buffer[f32] = b
    n = len(b2)
  }
  n
}
main: (): i32 = 0
`, "created only by c.own"},
		"parameter":    {"f: (b: Buffer[f32]): u32 = len(b)\nmain: (): i32 = 0\n", "cannot be a parameter"},
		"record field": {"W: type = struct { b: Buffer[f32] }\nmain: (): i32 = 0\n", "cannot be a record field"},
		"return":       {"f: (b: u32): Buffer[f32] { unsafe { x: Buffer[f32] = c.own[f32](c.Ptr(u32(0)), b) } }\nmain: (): i32 = 0\n", "cannot be returned"},
		"argument": {prelude + `
id[T]: (x: T): T = x
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
    n = len(id(b))
  }
  n
}
main: (): i32 = 0
`, "cannot instantiate id"},
		"direct index": {prelude + `
f: (): f32 {
  x: f32 = 0.0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
    x = b[0]
  }
  x
}
main: (): i32 = 0
`, "indexed through a borrow"},
		"element type": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[string] = c.own[string](malloc(c.Size(u32(64))), u32(16))
    n = len(b)
  }
  n
}
main: (): i32 = 0
`, "boundary type"},
		"use after disown": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
    q: c.Ptr = c.disown(b)
    v: []f32 = view(&b)
    n = len(v)
  }
  n
}
main: (): i32 = 0
`, "OAK-B0111"},
		"disown while borrowed": {prelude + `
f: (): u32 {
  n: u32 = 0
  unsafe {
    b: Buffer[f32] = c.own[f32](malloc(c.Size(u32(64))), u32(16))
    v: []f32 = view(&b)
    q: c.Ptr = c.disown(b)
    n = len(v)
  }
  n
}
main: (): i32 = 0
`, "cannot be handed back while borrow"},
	}
	for name, c := range cases {
		_, err := New().WithSource(name+".oak", c.src).EmitC().Get()
		if err == nil {
			t.Fatalf("%s: expected a diagnostic mentioning %q", name, c.want)
		}
		if !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: diagnostics should mention %q, got:\n%v", name, c.want, err)
		}
	}
}
