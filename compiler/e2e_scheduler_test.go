package compiler

import "testing"

// The intrusive-container pattern of Linux (list_head), SerenityOS
// (IntrusiveList), and Fuchsia (fbl::DoublyLinkedList), in Oak doctrine:
// nodes live in a static pool, links are typed indices — no pointer
// graphs, no container_of, bounds-checked by construction, and the links
// are smaller and cache-friendlier than pointers. A ready-queue over a
// Thread pool: unlink from the middle, push, pop — executed.
func TestE2ESchedulerReadyQueue(t *testing.T) {
	code, abnormal := buildAndRun(t, "sched", `
NONE: u32 = 255

Thread: type = struct {
  priority: u8
  next: u32
  prev: u32
}

pool: [8]Thread
readyHead: u32 = 255
readyTail: u32 = 255

enqueue: (id: u32): () {
  pool[id].next = NONE
  pool[id].prev = readyTail
  readyTail == NONE ? {
    readyHead = id
  } | {
    pool[readyTail].next = id
  }
  readyTail = id
}

unlink: (id: u32): () {
  pool[id].prev == NONE ? {
    readyHead = pool[id].next
  } | {
    pool[pool[id].prev].next = pool[id].next
  }
  pool[id].next == NONE ? {
    readyTail = pool[id].prev
  } | {
    pool[pool[id].next].prev = pool[id].prev
  }
}

dequeue: (): u32 {
  id: u32 = readyHead
  unlink(id)
  id
}

main: (): i32 {
  pool[u32(1)].priority = u8(10)
  pool[u32(3)].priority = u8(30)
  pool[u32(5)].priority = u8(50)
  enqueue(u32(1))
  enqueue(u32(3))
  enqueue(u32(5))
  unlink(u32(3))
  a: u32 = dequeue()
  b: u32 = dequeue()
  assert(readyHead == NONE && readyTail == NONE)
  i32_bits_u32(a * u32(10) + b) + i32(pool[b].priority) - 23
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (15 + 50 - 23)", code, abnormal)
	}
}
