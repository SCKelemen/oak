package compiler

import "testing"

// Phantom-typed intrusive links: Idx[P] is a one-field generic record — a
// zero-cost typed index after monomorphization (oak_Idx_Thread is a
// 4-byte struct, layout-asserted). Queue A's links cannot be fed to pool
// B: Idx[Thread] and Idx[Timer] share a shape and are distinct nominal
// types. The ready-queue from the scheduler test, retyped.
func TestE2EPhantomTypedLinks(t *testing.T) {
	code, abnormal := buildAndRun(t, "typedlinks", `
Idx[P]: type = struct { raw: u32 }

Thread: type = struct {
  priority: u8
  next: Idx[Thread]
}

Timer: type = struct { deadline: u32 }

pool: [8]Thread
freeHead: Idx[Thread]

seed_free_list: (): () {
  i: u32 = 0
  while i < u32(8) {
    pool[i].next.raw = i
    i = i + 1
  }
  freeHead.raw = u32(8)
}

acquire: (): u32 {
  assert(freeHead.raw != u32(0))
  id: u32 = freeHead.raw - u32(1)
  freeHead = pool[id].next
  id
}

release: (id: u32): () {
  pool[id].next = freeHead
  freeHead.raw = id + u32(1)
}

main: (): i32 {
  seed_free_list()
  a: u32 = acquire()
  b: u32 = acquire()
  assert(a == 7 && b == 6)
  release(a)
  c: u32 = acquire()
  assert(c == 7)
  pool[c].priority = u8(42)
  i32(pool[u32(7)].priority)
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
