package compiler

import "testing"

// The slab package (stdlib/slab.oak; docs/spec/60-effects-allocation.md
// §7–§8): a bounded typed slab over caller-owned storage. The laws under
// test are Oak.Slab's (live never exceeds capacity; allocation from a full
// slab fails explicitly and changes nothing) and Oak.Handles' (a handle
// that resolved before its slot's reuse does not resolve to the replacement;
// a retired slot is never handed out). Both realizations run it.
const slabProgram = `package main

import("slab")

main: (): i32 {
  slots: [4]slab.SlabSlot
  payload: [4]u32
  s: slab.Slab = slab.slab_init(span(&slots))
  assert(slab.slab_live(s) == u32(0))
  assert(slab.slab_remaining(s) == u32(4))

  a: slab.SlabAlloc = slab.slab_alloc(s, span(&slots))
  b: slab.SlabAlloc = slab.slab_alloc(a.slab, span(&slots))
  c: slab.SlabAlloc = slab.slab_alloc(b.slab, span(&slots))
  d: slab.SlabAlloc = slab.slab_alloc(c.slab, span(&slots))
  assert(a.ok && b.ok && c.ok && d.ok)
  assert(a.handle.slot == u32(0) && b.handle.slot == u32(1) && c.handle.slot == u32(2) && d.handle.slot == u32(3))
  assert(slab.slab_live(d.slab) == u32(4))
  payload[a.handle.slot] = u32(10)
  payload[b.handle.slot] = u32(20)
  payload[c.handle.slot] = u32(30)
  payload[d.handle.slot] = u32(40)

  // Full: the fifth allocation fails and leaves the slab as it was.
  e: slab.SlabAlloc = slab.slab_alloc(d.slab, span(&slots))
  assert(!e.ok)
  assert(slab.slab_live(e.slab) == u32(4) && slab.slab_remaining(e.slab) == u32(0))

  // Free b: its handle stops resolving, a second free is refused.
  fb: slab.SlabFree = slab.slab_free(e.slab, span(&slots), b.handle)
  assert(fb.ok && slab.slab_live(fb.slab) == u32(3))
  assert(!slab.slab_resolves(span(&slots), b.handle))
  fb2: slab.SlabFree = slab.slab_free(fb.slab, span(&slots), b.handle)
  assert(!fb2.ok && slab.slab_live(fb2.slab) == u32(3))

  // Reuse: slot 1 comes back with the next generation; the stale handle
  // still does not resolve, the new one does, and the payload is the new
  // object's.
  b2: slab.SlabAlloc = slab.slab_alloc(fb2.slab, span(&slots))
  assert(b2.ok && b2.handle.slot == u32(1) && b2.handle.generation == u32(2))
  assert(!slab.slab_resolves(span(&slots), b.handle))
  assert(slab.slab_resolves(span(&slots), b2.handle))
  payload[b2.handle.slot] = u32(21)
  assert(payload[b.handle.slot] == u32(21))

  // Retirement: a slot whose generation cannot advance is dropped from the
  // free list rather than reused, so the slab is full with one slot free.
  fc: slab.SlabFree = slab.slab_free(b2.slab, span(&slots), c.handle)
  assert(fc.ok)
  slots[2].generation = slab.slab_retired()
  r: slab.SlabAlloc = slab.slab_alloc(fc.slab, span(&slots))
  assert(!r.ok)
  fd: slab.SlabFree = slab.slab_free(r.slab, span(&slots), d.handle)
  assert(fd.ok)
  d2: slab.SlabAlloc = slab.slab_alloc(fd.slab, span(&slots))
  assert(d2.ok && d2.handle.slot == u32(3) && d2.handle.generation == u32(2))
  assert(slab.slab_live(d2.slab) == u32(3))

  i32_bits_u32(payload[a.handle.slot] + payload[b2.handle.slot] + u32(11))
}
`

func slabModule(t *testing.T) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/slab_check\noak 0.1.0\n",
		"main.oak": slabProgram,
	})
}

func TestE2ESlabInterpreted(t *testing.T) {
	if got := interpretModule(t, slabModule(t)); got != 42 {
		t.Fatalf("main() returned %d, want 42", got)
	}
}

func TestE2ESlabCompiled(t *testing.T) {
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(slabModule(t)))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
