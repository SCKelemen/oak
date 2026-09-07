package compiler

import "testing"

// Const parameters and generic records (docs/spec/20-types.md,
// docs/spec/40-records.md): Ring[T, N] — the hypervisor pilot's queue
// shape — as a zero-initialized static global, with field mutation,
// array-field stores through the proven layout, and % arithmetic.
func TestE2ERingBuffer(t *testing.T) {
	code, abnormal := buildAndRun(t, "ring", `
Ring[T, N: u32]: type = struct {
  buffer: [N]T
  head: u32
  count: u32
}

events: Ring[u8, 8]

push: (v: u8): () {
  events.buffer[(events.head + events.count) % u32(8)] = v
  events.count = events.count + 1
}

pop: (): u8 {
  v: u8 = events.buffer[events.head]
  events.head = (events.head + u32(1)) % u32(8)
  events.count = events.count - 1
  v
}

main: (): i32 {
  push(u8(7))
  push(u8(11))
  push(u8(20))
  a: u8 = pop()
  b: u8 = pop()
  assert(events.count == u32(1))
  i32(a) + i32(b) + i32(pop()) + 4
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (7 + 11 + 20 + 4)", code, abnormal)
	}
}
