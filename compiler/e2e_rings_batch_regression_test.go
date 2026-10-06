package compiler

import "testing"

// Exercise both backends of the language, not a second hand-written queue.
// These checks are sequential API-composition regressions; the existing
// threaded ring tests cover concurrent publication separately.
func checkSpscBatchProgram(t *testing.T, program string) {
	t.Helper()
	want := interpretModule(t, ringsModule(t, program))
	exit, abnormal := buildPackageAndRun(t, New().WithPackageDir(ringsModule(t, program)))
	if abnormal || int64(exit) != want || exit != 42 {
		t.Fatalf("interpreter %d, compiled exit %d abnormal %v, want 42", want, exit, abnormal)
	}
}

func TestE2ERingsSpscMixedBulkScalar(t *testing.T) {
	checkSpscBatchProgram(t, `package main

import("rings")

main: (): i32 {
  state: [1]rings.SpscCursor
  batch_state: [1]rings.SpscProducerBatch
  data: [8]u32
  input: [4]u32 = [4]u32{ 10, 11, 12, 13 }
  cursor: [*]rings.SpscCursor = span(&state)
  batch: [*]rings.SpscProducerBatch = span(&batch_state)

  // Cold cache: consuming the whole batch must leave scalar pop empty.
  assert(rings.spsc_reserve(cursor, batch, u32(8), u32(4)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(4))
  assert(rings.spsc_commit(cursor, batch, u32(4)))
  assert(rings.spsc_consume[u32](cursor, span(&data), u32(4)))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))
  assert(rings.spsc_count(cursor) == u32(0))

  // Warm a scalar observation, then publish beyond it. Bulk consumption
  // must not leave tail_seen behind the new head. Repeat through slot wrap.
  round: u32 = u32(0)
  while round < u32(32) {
    assert(rings.spsc_reserve(cursor, batch, u32(8), u32(4)))
    assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(4))
    assert(rings.spsc_commit(cursor, batch, u32(4)))
    assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(10))
    assert(rings.spsc_push[u32](cursor, span(&data), u32(14)))
    assert(rings.spsc_push[u32](cursor, span(&data), u32(15)))
    assert(rings.spsc_count(cursor) == u32(5))
    assert(!rings.spsc_consume[u32](cursor, span(&data), u32(6)))
    assert(rings.spsc_count(cursor) == u32(5))
    assert(rings.spsc_consume[u32](cursor, span(&data), u32(0)))
    assert(rings.spsc_consume[u32](cursor, span(&data), u32(4)))
    assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(15))
    assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))
    assert(rings.spsc_count(cursor) == u32(0))
    round = round + u32(1)
  }
  i32(42)
}
`)
}

func TestE2ERingsSpscBatchPublicationAndRefusal(t *testing.T) {
	checkSpscBatchProgram(t, `package main

import("rings")

main: (): i32 {
  state: [1]rings.SpscCursor
  batch_state: [1]rings.SpscProducerBatch
  data: [4]u32
  other: [8]u32
  input: [6]u32 = [6]u32{ 1, 2, 3, 4, 5, 6 }
  cursor: [*]rings.SpscCursor = span(&state)
  batch: [*]rings.SpscProducerBatch = span(&batch_state)

  assert(!rings.spsc_reserve(cursor, batch, u32(4), u32(0)))
  assert(!rings.spsc_reserve(cursor, batch, u32(4), u32(5)))
  assert(!rings.spsc_commit(cursor, batch, u32(0)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(0))

  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(3)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(3))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(0))
  // Staged payload is invisible until commit, including to a zero-copy reader.
  {
    pending: []u32 = rings.spsc_run[u32](cursor, view(&data))
    assert(len(pending) == u32(0))
  }
  assert(rings.spsc_count(cursor) == u32(0))
  assert(!rings.spsc_commit(cursor, batch, u32(4)))
  assert(rings.spsc_count(cursor) == u32(0))
  // Publish only a written prefix; the abandoned third slot is not a message.
  assert(rings.spsc_commit(cursor, batch, u32(2)))
  assert(!rings.spsc_commit(cursor, batch, u32(2)))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(1))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(2))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))

  // An active reservation can be explicitly abandoned with commit(0).
  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(2)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(2))
  assert(rings.spsc_commit(cursor, batch, u32(0)))
  assert(rings.spsc_count(cursor) == u32(0))
  assert(!rings.spsc_commit(cursor, batch, u32(1)))

  // Refuse a different storage shape before any payload write.
  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(2)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&other), view(&input)) == u32(0))
  assert(other[0] == u32(0))
  assert(!rings.spsc_commit(cursor, batch, u32(1)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(2))
  // Mixing a scalar push into an open reservation invalidates its saved tail.
  assert(rings.spsc_push[u32](cursor, span(&data), u32(99)))
  assert(!rings.spsc_commit(cursor, batch, u32(2)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(0))
  assert(rings.spsc_count(cursor) == u32(1))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(99))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))

  // A failed reservation replaces the old uncommitted claim without publishing.
  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(1)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(1))
  assert(!rings.spsc_reserve(cursor, batch, u32(4), u32(5)))
  assert(!rings.spsc_commit(cursor, batch, u32(1)))
  assert(rings.spsc_count(cursor) == u32(0))

  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(4)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(4))
  assert(rings.spsc_commit(cursor, batch, u32(4)))
  assert(!rings.spsc_reserve(cursor, batch, u32(4), u32(1)))
  assert(!rings.spsc_push[u32](cursor, span(&data), u32(99)))
  assert(rings.spsc_count(cursor) == u32(4))
  assert(rings.spsc_consume[u32](cursor, span(&data), u32(4)))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))
  i32(42)
}
`)
}

func TestE2ERingsSpscBatchCounterRollover(t *testing.T) {
	checkSpscBatchProgram(t, `package main

import("rings")

main: (): i32 {
  state: [1]rings.SpscCursor
  batch_state: [1]rings.SpscProducerBatch
  data: [4]u32
  input: [4]u32 = [4]u32{ 101, 102, 103, 104 }
  cursor: [*]rings.SpscCursor = span(&state)
  batch: [*]rings.SpscProducerBatch = span(&batch_state)
  // Offline initialization only: no endpoint has been published to a thread.
  near_wrap: u32 = u32(4294967294)
  atomic_store_relaxed(cursor[0].head, near_wrap)
  atomic_store_relaxed(cursor[0].tail, near_wrap)
  cursor[0].head_seen = near_wrap
  cursor[0].tail_seen = near_wrap

  assert(rings.spsc_reserve(cursor, batch, u32(4), u32(4)))
  assert(rings.spsc_put_run[u32](cursor, batch, span(&data), view(&input)) == u32(4))
  assert(rings.spsc_commit(cursor, batch, u32(4)))
  assert(atomic_load_relaxed(cursor[0].tail) == u32(2))
  assert(rings.spsc_count(cursor) == u32(4))
  assert(!rings.spsc_push[u32](cursor, span(&data), u32(999)))
  {
    first: []u32 = rings.spsc_run[u32](cursor, view(&data))
    assert(len(first) == u32(2))
    assert(first[0] == u32(101) && first[1] == u32(102))
  }
  assert(rings.spsc_consume[u32](cursor, span(&data), u32(2)))
  assert(atomic_load_relaxed(cursor[0].head) == u32(0))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(103))
  {
    last: []u32 = rings.spsc_run[u32](cursor, view(&data))
    assert(len(last) == u32(1) && last[0] == u32(104))
  }
  assert(rings.spsc_consume[u32](cursor, span(&data), u32(1)))
  assert(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)) == u32(777))
  assert(rings.spsc_count(cursor) == u32(0))
  assert(rings.spsc_push[u32](cursor, span(&data), u32(42)))
  i32_bits_u32(option_or[u32](rings.spsc_pop[u32](cursor, span(&data)), u32(777)))
}
`)
}
