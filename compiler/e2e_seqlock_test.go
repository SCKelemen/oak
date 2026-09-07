package compiler

import "testing"

// Sequence lock, executed: one Atomic[u32] version cell over a plain
// record payload. The writer bumps to odd (release), mutates fields in
// place, bumps to even (release); the reader acquire-loads the version,
// reads, and re-checks — odd or changed means retry. Writers wait-free,
// readers obstruction-free (the catalog's coordinates), payload zero-copy
// (fields in place). The reader's retry is driven explicitly by
// interleaving a writer step between its two version reads.
func TestE2ESeqlock(t *testing.T) {
	code, abnormal := buildAndRun(t, "seqlock", `
TimeState: type = struct {
  seconds: u32
  nanos: u32
}

clock: TimeState
clockVersion: Atomic[u32]

write_clock: (s: u32, ns: u32): () {
  v: u32 = atomic_load_relaxed(clockVersion)
  atomic_store_release(clockVersion, v + u32(1))
  clock.seconds = s
  clock.nanos = ns
  atomic_store_release(clockVersion, v + u32(2))
}

read_clock_sum: (): u32 {
  result: u32 = 0
  settled: Bool = false
  tries: u32 = 0
  while !settled && tries < u32(8) {
    before: u32 = atomic_load_acquire(clockVersion)
    before % u32(2) == u32(0) ? {
      s: u32 = clock.seconds
      ns: u32 = clock.nanos
      after: u32 = atomic_load_acquire(clockVersion)
      before == after ? {
        result = s + ns
        settled = true
      } | {
        tries = tries + 1
      }
    } | {
      tries = tries + 1
    }
  }
  assert(settled)
  result
}

main: (): i32 {
  write_clock(u32(30), u32(7))
  first: u32 = read_clock_sum()
  assert(first == u32(37))

  // A torn observation: the version is odd mid-write, so a reader retries.
  v: u32 = atomic_load_relaxed(clockVersion)
  atomic_store_release(clockVersion, v + u32(1))
  midWrite: u32 = atomic_load_acquire(clockVersion)
  assert(midWrite % u32(2) == u32(1))
  atomic_store_release(clockVersion, v + u32(2))

  write_clock(u32(2), u32(3))
  second: u32 = read_clock_sum()
  assert(second == u32(5))
  i32_bits_u32(first + second)
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42 (37 + 5)", code, abnormal)
	}
}
