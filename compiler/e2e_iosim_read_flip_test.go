package compiler

import "testing"

// A bit flip injected on the read half of a read-modify-write must make
// the file untrusted (docs/notes/oak-requests-2026-09-13.md finding 3):
// the flipped bytes are written back by a clean store, which heals the
// block's own fault flags, so the entry — not the block — has to remember
// the lie. With flips the only enabled fault, a sweep of seeded choice
// tapes writes two eight-byte records into one block (the second write's
// read half re-reads the first record) and reads them back: whenever the
// bytes differ from what was written, the file must not be trusted. The
// laundering case — a flip landing in the first record during the second
// write's read — occurs in about one run in sixty-four, so the sweep
// insists on seeing mismatches at all.
func TestE2EIoSimReadFlipMarksEntryLied(t *testing.T) {
	program := `package main

import("iosim")

// One run under one tape: 1 when the bytes read back differ from the bytes
// written, plus 2 when the simulator still calls the file trusted.
run: (ring: [*]iosim.IoRing, requests: [*]iosim.IoRequest, completions: [*]iosim.IoCompletion, region: [*]u8, tape: []u8): u32 {
  iosim.io_attach(tape, u32(16))
  iosim.io_open_region(ring, region, u32(2))
  region[0] = u8(97)
  region[1] = u8(0)
  i: u32 = u32(0)
  while i < u32(16) {
    region[u32(32) + i] = u8_trunc_u32(u32(100) + i)
    i = i + u32(1)
  }
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_open(), u32(0), u64(0), u32(0), u32(2), u64(1), false)))
  assert(iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1) && completions[0].error == u32(0))
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_pwrite(), u32(0), u64(0), u32(32), u32(8), u64(2), false)))
  assert(iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  first_ok: Bool = completions[0].error == u32(0)
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_pwrite(), u32(0), u64(8), u32(40), u32(8), u64(3), false)))
  assert(iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  second_ok: Bool = completions[0].error == u32(0)
  // fsync: the durable copy takes the clean store, so a healed block is
  // clean on both copies and only the entry's ledger can remember the lie.
  assert(iosim.io_submit(ring, requests, iosim.io_request(iosim.io_op_fsync(), u32(0), u64(0), u32(0), u32(0), u64(5), false)))
  assert(iosim.io_wait(ring, requests, completions, region, u32(1)) == u32(1))
  synced: Bool = completions[0].error == u32(0)
  c: iosim.IoCompletion = iosim.io_pread_sync(ring, requests, completions, region, u32(0), u64(0), iosim.io_buffer(u32(64), u32(16)), u64(4))
  !(first_ok && second_ok && synced && c.error == u32(0) && c.result == u32(16)) ? { u32(0) } | {
    same: Bool = true
    i = u32(0)
    while i < u32(16) {
      region[u32(64) + i] != region[u32(32) + i] ? { same = false }
      i = i + u32(1)
    }
    same ? { u32(0) } | { iosim.iosim_trusted(u32(0)) ? { u32(3) } | { u32(1) } }
  }
}

main: (): i32 {
  ring_store: [1]iosim.IoRing
  req_store: [8]iosim.IoRequest
  cq_store: [8]iosim.IoCompletion
  region_store: iosim.IoSectorRegion[8192]
  tape: [64]u8
  ring: [*]iosim.IoRing = span(&ring_store)
  requests: [*]iosim.IoRequest = span(&req_store)
  completions: [*]iosim.IoCompletion = span(&cq_store)
  region: [*]u8 = span(&region_store.bytes)
  seed: u32 = u32(2463534242)
  mismatches: u32 = u32(0)
  laundered: u32 = u32(0)
  runs: u32 = u32(0)
  while runs < u32(512) {
    i: u32 = u32(0)
    while i < u32(64) {
      seed = seed * u32(1103515245) + u32(12345)
      tape[i] = u8_trunc_u32(seed >> u32(16))
      i = i + u32(1)
    }
    outcome: u32 = run(ring, requests, completions, region, view(&tape))
    outcome != u32(0) ? { mismatches = mismatches + u32(1) }
    outcome == u32(3) ? { laundered = laundered + u32(1) }
    runs = runs + u32(1)
  }
  laundered > u32(0) ? 2 | (mismatches == u32(0) ? 1 | 42)
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/readflip\noak 0.1.0\n",
		"main.oak": program,
	})
	// The simulator imports the testing host, which only `oak test` links;
	// the interpreter is the realization that runs here.
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("main() = %d, want 42 (1: no run ever read back a flipped byte; 2: a laundered flip left the file trusted)", got)
	}
}
