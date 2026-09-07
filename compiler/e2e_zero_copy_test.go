package compiler

import (
	"strings"
	"testing"
)

// The canonical Vyukov MPSC (DV-MPSC), index-linked: the producer's claim
// is ONE unconditional atomic_exchange — wait-free, no retry loop — followed
// by the plain next-link store. Those two steps create the publication
// window that makes the algorithm blocking overall and serializable rather
// than linearizable (int08h.com, "Ode to a Vyukov Queue"); the consumer API
// makes the window a named state: Item / Empty / Busy. The test drives the
// window explicitly by splitting claim and link.
// v1 honesty: node links are plain fields ordered by the exchange; a
// cross-core deployment wants atomic record fields, a recorded gap.
func TestE2EDvMpsc(t *testing.T) {
	code, abnormal := buildAndRun(t, "dvmpsc", `
Pop: type = Item: u8 | Empty | Busy

Node: type = struct {
  value: u8
  next: u32
}

nodes: [8]Node
dvHead: Atomic[u32]
dvTail: u32 = 1

dv_claim: (id: u32): u32 {
  nodes[id].next = u32(0)
  atomic_exchange_acq_rel(dvHead, id + u32(1))
}

dv_link: (prev: u32, id: u32): () {
  nodes[prev - u32(1)].next = id + u32(1)
}

dv_push: (id: u32, v: u8): () {
  nodes[id].value = v
  prev: u32 = dv_claim(id)
  dv_link(prev, id)
}

dv_pop: (): Pop {
  following: u32 = nodes[dvTail - u32(1)].next
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

  dv_pop() ?
    | .Empty => { assert(true) }
    | .Item(v) => { assert(false) }
    | .Busy => { assert(false) }

  dv_push(u32(1), u8(21))

  first: u8 = dv_pop() ?
    | .Item(v) => v
    | .Empty => u8(0)
    | .Busy => u8(0)
  assert(first == u8(21))

  stalledPrev: u32 = dv_claim(u32(2))
  nodes[u32(2)].value = u8(9)
  sawBusy: Bool = dv_pop() ?
    | .Busy => true
    | .Item(v) => false
    | .Empty => false
  assert(sawBusy)

  dv_link(stalledPrev, u32(2))
  second: u8 = dv_pop() ?
    | .Item(v) => v
    | .Empty => u8(0)
    | .Busy => u8(0)
  assert(second == u8(9))

  i32(first) + i32(second) + 12
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (21 + 9 + 12)", code, abnormal)
	}
}

// Zero-copy SPSC: reserve/fill-in-place/commit. Record payloads are built
// field-by-field inside their pool slot and read in place by the consumer —
// only u32 indices cross the boundary, and the emitted C contains no
// Packet-typed copy anywhere (asserted below). Zero allocation is the
// language default; zero copy is this shape.
func TestE2EZeroCopySpsc(t *testing.T) {
	src := `
Packet: type = struct {
  kind: u8
  a: u32
  b: u32
}

packets: [4]Packet
zcHead: Atomic[u32]
zcTail: Atomic[u32]

zc_produce: (kind: u8, a: u32, b: u32): Bool {
  t: u32 = atomic_load_relaxed(zcTail)
  h: u32 = atomic_load_acquire(zcHead)
  t - h == u32(4) ? { false } | {
    slot: u32 = t % u32(4)
    packets[slot].kind = kind
    packets[slot].a = a
    packets[slot].b = b
    atomic_store_release(zcTail, t + u32(1))
    true
  }
}

zc_consume: (): u32 {
  h: u32 = atomic_load_relaxed(zcHead)
  t: u32 = atomic_load_acquire(zcTail)
  h == t ? { u32(0) } | {
    slot: u32 = h % u32(4)
    sum: u32 = u32(packets[slot].kind) + packets[slot].a + packets[slot].b
    atomic_store_release(zcHead, h + u32(1))
    sum
  }
}

main: (): i32 {
  assert(zc_produce(u8(1), u32(2), u32(3)))
  assert(zc_produce(u8(4), u32(5), u32(6)))
  first: u32 = zc_consume()
  second: u32 = zc_consume()
  assert(first == u32(6) && second == u32(15))
  assert(zc_consume() == u32(0))
  i32_bits_u32(first + second) + 21
}
`
	output, err := New().WithSource("zcspsc.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	// Zero-copy, verified in the artifact: the only oak_Packet occurrences
	// are the typedef, its layout assertions (sizeof/offsetof), and the
	// pool declarator — never a compound literal, a Packet-typed local or
	// temporary, or a whole-element load into a variable.
	for _, copyForm := range []string{"((oak_Packet)", "oak_Packet oak_scrutinee", " = oak_index( packets", "oak_Packet v ", "oak_Packet tmp"} {
		if strings.Contains(output, copyForm) {
			t.Fatalf("Packet copy form %q found in emitted C:\n%s", copyForm, output)
		}
	}

	code, abnormal := buildAndRun(t, "zcspsc", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (21 + 21)", code, abnormal)
	}
}
