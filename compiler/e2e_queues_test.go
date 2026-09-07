package compiler

import "testing"

// SPSC ring, written in Oak over the atomics surface (docs/spec/65): two
// free-running Atomic[u32] indices, plain slot writes published by a
// release store of the producer index, consumed under an acquire load —
// recipe 1's causal publish, wait-free bounded per operation. The
// single-threaded run verifies the protocol logic: full detection, FIFO
// order, empty pop.
func TestE2ESpscRing(t *testing.T) {
	code, abnormal := buildAndRun(t, "spsc", `
Option[T]: type = Some: T | None

slots: [8]u8
spscHead: Atomic[u32]
spscTail: Atomic[u32]

spsc_push: (v: u8): Bool {
  t: u32 = atomic_load_relaxed(spscTail)
  h: u32 = atomic_load_acquire(spscHead)
  t - h == u32(8) ? { false } | {
    slots[t % u32(8)] = v
    atomic_store_release(spscTail, t + u32(1))
    true
  }
}

spsc_pop: (): Option[u8] {
  h: u32 = atomic_load_relaxed(spscHead)
  t: u32 = atomic_load_acquire(spscTail)
  h == t ? { .None } | {
    v: u8 = slots[h % u32(8)]
    atomic_store_release(spscHead, h + u32(1))
    .Some(v)
  }
}

main: (): i32 {
  i: u32 = 0
  while i < u32(8) {
    assert(spsc_push(u8_trunc_u32(u32(10) + i)))
    i = i + 1
  }
  assert(!spsc_push(u8(99)))

  first: u8 = spsc_pop() ?
    | .Some(v) => v
    | .None => u8(0)
  second: u8 = spsc_pop() ?
    | .Some(v) => v
    | .None => u8(0)
  assert(first == u8(10) && second == u8(11))

  assert(spsc_push(u8(77)))

  drained: u32 = 0
  more: Bool = true
  while more {
    spsc_pop() ?
      | .Some(v) => {
        drained = drained + u32(1)
      }
      | .None => {
        more = false
      }
  }
  assert(drained == u32(7))
  i32(first) + i32(second) + i32_bits_u32(drained) + 14
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (10 + 11 + 7 + 14)", code, abnormal)
	}
}

// MPSC intake, Vyukov LIFO-grab shape: producers CAS-push pool indices
// (index+1 encoding so the zero-initialized head means empty) with release
// order — the lock-free rung, visible as a bounded asserted retry loop;
// the consumer grabs the whole chain with one CAS to empty, reverses in
// place to FIFO, and walks it. Recipe 2's mailbox, executed.
func TestE2EMpscIntake(t *testing.T) {
	code, abnormal := buildAndRun(t, "mpsc", `
Msg: type = struct {
  value: u8
  next: u32
}

msgs: [8]Msg
mpscHead: Atomic[u32]

mpsc_push: (id: u32, v: u8): () {
  msgs[id].value = v
  observed: u32 = atomic_load_relaxed(mpscHead)
  claimed: Bool = false
  tries: u32 = 0
  while !claimed && tries < u32(64) {
    msgs[id].next = observed
    prior: u32 = atomic_compare_exchange_release_relaxed(mpscHead, observed, id + u32(1))
    prior == observed ? {
      claimed = true
    } | {
      observed = prior
      tries = tries + 1
    }
  }
  assert(claimed)
}

mpsc_grab: (): u32 {
  top: u32 = atomic_load_acquire(mpscHead)
  grabbed: u32 = 0
  done: Bool = false
  while !done {
    top == u32(0) ? {
      done = true
    } | {
      prior: u32 = atomic_compare_exchange_acq_rel_acquire(mpscHead, top, u32(0))
      prior == top ? {
        grabbed = top
        done = true
      } | {
        top = prior
      }
    }
  }
  grabbed
}

reverse: (lifo: u32): u32 {
  fifo: u32 = 0
  cur: u32 = lifo
  while cur != u32(0) {
    id: u32 = cur - u32(1)
    following: u32 = msgs[id].next
    msgs[id].next = fifo
    fifo = cur
    cur = following
  }
  fifo
}

main: (): i32 {
  mpsc_push(u32(0), u8(5))
  mpsc_push(u32(1), u8(6))
  mpsc_push(u32(2), u8(7))

  fifo: u32 = reverse(mpsc_grab())
  assert(atomic_load_acquire(mpscHead) == u32(0))

  checksum: u32 = 0
  position: u32 = 1
  cur: u32 = fifo
  while cur != u32(0) {
    id: u32 = cur - u32(1)
    checksum = checksum + position * u32(msgs[id].value)
    position = position + 1
    cur = msgs[id].next
  }
  assert(checksum == u32(38))
  i32_bits_u32(checksum) + 4
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (1*5 + 2*6 + 3*7 + 4)", code, abnormal)
	}
}
