package compiler

import "testing"

// The faithful DV-MPSC (1024cores, "intrusive MPSC node-based queue"):
// with atomic record fields landed, the next links are Atomic[u32] cells —
// the producer's link store is a release on the field cell and the
// consumer's traversal an acquire load, the real cross-core protocol
// rather than plain fields ordered by the exchange.
func TestE2EDvMpscAtomicLinks(t *testing.T) {
	code, abnormal := buildAndRun(t, "dvatomic", `
Pop: type = Item: u8 | Empty | Busy

Node: type = struct {
  value: u8
  next: Atomic[u32]
}

nodes: [8]Node
dvHead: Atomic[u32]
dvTail: u32 = 1

dv_push: (id: u32, v: u8): () {
  nodes[id].value = v
  atomic_store_relaxed(nodes[id].next, u32(0))
  prev: u32 = atomic_exchange_acq_rel(dvHead, id + u32(1))
  atomic_store_release(nodes[prev - u32(1)].next, id + u32(1))
}

dv_pop: (): Pop {
  following: u32 = atomic_load_acquire(nodes[dvTail - u32(1)].next)
  following == u32(0) ? {
    head: u32 = atomic_load_acquire(dvHead)
    head == dvTail ? { .Empty } | { .Busy }
  } | {
    dvTail = following
    .Item(nodes[following - u32(1)].value)
  }
}

main: (): i32 {
  atomic_store_relaxed(dvHead, u32(1))
  dv_push(u32(1), u8(21))
  dv_push(u32(2), u8(9))
  first: u8 = dv_pop() ?
    | .Item(v) => v
    | .Empty => u8(0)
    | .Busy => u8(0)
  second: u8 = dv_pop() ?
    | .Item(v) => v
    | .Empty => u8(0)
    | .Busy => u8(0)
  sawEmpty: Bool = dv_pop() ?
    | .Empty => true
    | .Item(v) => false
    | .Busy => false
  assert(sawEmpty)
  i32(first) + i32(second) + 12
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (21 + 9 + 12)", code, abnormal)
	}
}

// The Vyukov bounded MPMC (1024cores, "bounded MPMC queue"): per-slot
// sequence cells ([N]Atomic[u32]) carry the handshake — a slot is
// enqueue-ready when seq == pos, dequeue-ready when seq == pos + 1, and
// recycled at seq = pos + N. Lock-free both sides (bounded, asserted
// retries); wrapping position arithmetic compared through signed bits.
func TestE2EBoundedMpmc(t *testing.T) {
	code, abnormal := buildAndRun(t, "mpmc", `
seqs: [4]Atomic[u32]
slots: [4]u32
enqPos: Atomic[u32]
deqPos: Atomic[u32]

mpmc_init: (): () {
  i: u32 = 0
  while i < u32(4) {
    atomic_store_relaxed(seqs[i], i)
    i = i + 1
  }
}

mpmc_enqueue: (v: u32): Bool {
  done: Bool = false
  full: Bool = false
  tries: u32 = 0
  pos: u32 = atomic_load_relaxed(enqPos)
  while !done && !full && tries < u32(64) {
    cell: u32 = pos % u32(4)
    seq: u32 = atomic_load_acquire(seqs[cell])
    dif: i32 = i32_bits_u32(seq - pos)
    dif == 0 ? {
      prior: u32 = atomic_compare_exchange_relaxed_relaxed(enqPos, pos, pos + u32(1))
      prior == pos ? {
        slots[cell] = v
        atomic_store_release(seqs[cell], pos + u32(1))
        done = true
      } | {
        pos = prior
        tries = tries + 1
      }
    } | {
      dif < 0 ? {
        full = true
      } | {
        pos = atomic_load_relaxed(enqPos)
        tries = tries + 1
      }
    }
  }
  assert(done || full)
  done
}

mpmc_dequeue: (): i32 {
  done: Bool = false
  empty: Bool = false
  taken: u32 = 0
  tries: u32 = 0
  pos: u32 = atomic_load_relaxed(deqPos)
  while !done && !empty && tries < u32(64) {
    cell: u32 = pos % u32(4)
    seq: u32 = atomic_load_acquire(seqs[cell])
    dif: i32 = i32_bits_u32(seq - (pos + u32(1)))
    dif == 0 ? {
      prior: u32 = atomic_compare_exchange_relaxed_relaxed(deqPos, pos, pos + u32(1))
      prior == pos ? {
        taken = slots[cell]
        atomic_store_release(seqs[cell], pos + u32(4))
        done = true
      } | {
        pos = prior
        tries = tries + 1
      }
    } | {
      dif < 0 ? {
        empty = true
      } | {
        pos = atomic_load_relaxed(deqPos)
        tries = tries + 1
      }
    }
  }
  assert(done || empty)
  done ? { i32_bits_u32(taken) } | { 0 - 1 }
}

main: (): i32 {
  mpmc_init()
  assert(mpmc_enqueue(u32(10)))
  assert(mpmc_enqueue(u32(11)))
  assert(mpmc_enqueue(u32(12)))
  assert(mpmc_enqueue(u32(13)))
  assert(!mpmc_enqueue(u32(99)))

  a: i32 = mpmc_dequeue()
  b: i32 = mpmc_dequeue()
  assert(a == 10 && b == 11)

  assert(mpmc_enqueue(u32(14)))
  c: i32 = mpmc_dequeue()
  d: i32 = mpmc_dequeue()
  e: i32 = mpmc_dequeue()
  assert(mpmc_dequeue() == 0 - 1)
  a + b + c + d + e - 18
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (10+11+12+13+14 - 18)", code, abnormal)
	}
}
