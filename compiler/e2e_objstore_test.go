package compiler

import "testing"

// The object-store port's simulated realization (docs/spec/121-object-store.md;
// the dbs pilot's round-five item 16): put-if-generation and
// delete-if-generation over a bounded key table, generations from one
// monotone counter, and the two faults an object store has — a request the
// store never saw, and a mutation applied whose acknowledgement was lost.
// The simulator imports the testing module, which only `oak test` links,
// so the interpreter is the realization that runs here.
func TestE2EObjectStoreSemantics(t *testing.T) {
	program := `package main

import("objsim")

main: (): i32 {
  store_slot: [1]objsim.ObjStore
  region_store: [1024]u8
  tape: [4]u8
  store: [*]objsim.ObjStore = span(&store_slot)
  region: [*]u8 = span(&region_store)
  objsim.obj_attach(view(&tape), u32(0))
  objsim.obj_open_store(store, region)
  // key "a" at 0, key "b" at 8, values at 64 and 128, output at 256, listing at 512
  region[0] = u8(97)
  region[1] = u8(0)
  region[8] = u8(98)
  region[9] = u8(0)
  i: u32 = u32(0)
  while i < u32(8) {
    region[u32(64) + i] = u8_trunc_u32(u32(10) + i)
    region[u32(128) + i] = u8_trunc_u32(u32(20) + i)
    i = i + u32(1)
  }
  a: objsim.ObjWindow = objsim.obj_window(u32(0), u32(2))
  b: objsim.ObjWindow = objsim.obj_window(u32(8), u32(2))
  v1: objsim.ObjWindow = objsim.obj_window(u32(64), u32(8))
  v2: objsim.ObjWindow = objsim.obj_window(u32(128), u32(8))
  out: objsim.ObjWindow = objsim.obj_window(u32(256), u32(16))

  // A missing key: stat is NotFound, a put "if 7" is refused with absent.
  assert(objsim.obj_stat(store, region, a).error == objsim.obj_err_not_found())
  refused: objsim.ObjCompletion = objsim.obj_put(store, region, a, v1, u64(7))
  assert(refused.error == objsim.obj_err_precondition() && refused.generation == objsim.obj_absent())
  // Creation requires absence; the generation is 1.
  first: objsim.ObjCompletion = objsim.obj_put(store, region, a, v1, objsim.obj_absent())
  assert(first.error == u32(0) && first.generation == u64(1) && first.result == u32(8))
  // A second creation is refused with the current generation.
  again: objsim.ObjCompletion = objsim.obj_put(store, region, a, v1, objsim.obj_absent())
  assert(again.error == objsim.obj_err_precondition() && again.generation == u64(1))
  // Compare-and-set: exactly one of two "if 1" puts wins.
  win: objsim.ObjCompletion = objsim.obj_put(store, region, a, v2, u64(1))
  lose: objsim.ObjCompletion = objsim.obj_put(store, region, a, v1, u64(1))
  assert(win.error == u32(0) && win.generation == u64(2))
  assert(lose.error == objsim.obj_err_precondition() && lose.generation == u64(2))
  // The read sees the winner.
  got: objsim.ObjCompletion = objsim.obj_get(store, region, a, out)
  assert(got.error == u32(0) && got.generation == u64(2) && got.result == u32(8) && region[256] == u8(20) && region[263] == u8(27))
  // A window too small copies nothing.
  small: objsim.ObjCompletion = objsim.obj_get(store, region, a, objsim.obj_window(u32(256), u32(4)))
  assert(small.error == objsim.obj_err_too_large() && small.generation == u64(2))
  // Another key draws from the same counter; the listing names both.
  other: objsim.ObjCompletion = objsim.obj_put(store, region, b, v1, objsim.obj_any())
  assert(other.error == u32(0) && other.generation == u64(3))
  listed: objsim.ObjCompletion = objsim.obj_list(store, region, objsim.obj_window(u32(0), u32(0)), objsim.obj_window(u32(512), u32(64)))
  assert(listed.error == u32(0) && listed.result == u32(4) && region[512] == u8(97) && region[514] == u8(98))
  // Delete needs the precondition too; a re-created key is above the deleted one.
  stale: objsim.ObjCompletion = objsim.obj_delete(store, region, a, u64(1))
  assert(stale.error == objsim.obj_err_precondition() && stale.generation == u64(2))
  gone: objsim.ObjCompletion = objsim.obj_delete(store, region, a, u64(2))
  assert(gone.error == u32(0) && gone.generation == u64(2))
  assert(objsim.obj_stat(store, region, a).error == objsim.obj_err_not_found())
  back: objsim.ObjCompletion = objsim.obj_put(store, region, a, v1, objsim.obj_absent())
  assert(back.error == u32(0) && back.generation == u64(4))
  // Invalid windows: a key without its NUL.
  bad: objsim.ObjCompletion = objsim.obj_put(store, region, objsim.obj_window(u32(0), u32(1)), v1, objsim.obj_any())
  assert(bad.error == objsim.obj_err_invalid())
  42
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/objstore\noak 0.1.0\n",
		"main.oak": program,
	})
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("main() = %d, want 42", got)
	}
}

// Under seeded tapes with both faults enabled, the invariants of §3 hold
// whatever the store did: a mutation the caller was told succeeded saw the
// generation it named; the generation a stat reports never falls below one
// the caller was told; and a retry with a stale precondition after a lost
// acknowledgement is refused rather than applied twice. The sweep must
// observe lost acknowledgements, or it has tested nothing.
func TestE2EObjectStoreFaultSweep(t *testing.T) {
	program := `package main

import("objsim")

// One run: 100 puts on one key, each "if known", resynchronizing through
// stat after any Unavailable. Returns 0 when every invariant held, else a
// code naming the first violation.
run: (store: [*]objsim.ObjStore, region: [*]u8, tape: []u8): u32 {
  objsim.obj_attach(tape, u32(3))
  objsim.obj_open_store(store, region)
  region[0] = u8(107)
  region[1] = u8(0)
  key: objsim.ObjWindow = objsim.obj_window(u32(0), u32(2))
  value: objsim.ObjWindow = objsim.obj_window(u32(64), u32(4))
  known: u64 = objsim.obj_absent()
  outcome: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(100) && outcome == u32(0) {
    c: objsim.ObjCompletion = objsim.obj_put(store, region, key, value, known)
    c.error == u32(0) ? {
      // Applied: the new generation is above the one named.
      c.generation <= known ? { outcome = u32(1) } | { known = c.generation }
    } | {
      c.error == objsim.obj_err_precondition() ? {
        // Refused: only a lost acknowledgement can have moved the key past
        // what the caller knew, and the refusal names where it is now.
        c.generation < known ? { outcome = u32(2) } | { known = c.generation }
      } | {
        c.error == objsim.obj_err_unavailable() ? {
          s: objsim.ObjCompletion = objsim.obj_stat(store, region, key)
          s.error == u32(0) ? {
            s.generation < known ? { outcome = u32(3) } | { known = s.generation }
          } | { s.error != objsim.obj_err_unavailable() && s.error != objsim.obj_err_not_found() ? { outcome = u32(4) } }
        } | { outcome = u32(5) }
      }
    }
    i = i + u32(1)
  }
  outcome
}

main: (): i32 {
  store_slot: [1]objsim.ObjStore
  region_store: [256]u8
  tape: [200]u8
  store: [*]objsim.ObjStore = span(&store_slot)
  region: [*]u8 = span(&region_store)
  seed: u32 = u32(88172645)
  runs: u32 = u32(0)
  lost: u32 = u32(0)
  violation: u32 = u32(0)
  while runs < u32(64) && violation == u32(0) {
    i: u32 = u32(0)
    while i < u32(200) {
      seed = seed * u32(1103515245) + u32(12345)
      tape[i] = u8_trunc_u32(seed >> u32(16))
      i = i + u32(1)
    }
    violation = run(store, region, view(&tape))
    lost = lost + objsim.objsim_lost_acks()
    runs = runs + u32(1)
  }
  violation != u32(0) ? i32_bits_u32(violation) | (lost == u32(0) ? 1 | 42)
}
`
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/objsweep\noak 0.1.0\n",
		"main.oak": program,
	})
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("main() = %d, want 42 (1: no lost acknowledgement was ever injected; 2-5: an invariant failed)", got)
	}
}
