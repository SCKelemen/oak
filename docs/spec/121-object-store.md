# Object store: keyed objects with generation preconditions

Status: increment one is implemented — `objsim` (`stdlib/objsim.oak`), the
simulated realization, with the port surface below and `Oak.ObjectStore`
(`spec/lean/Oak/ObjectStore.lean`) proving the §3 contract over the model.
Increment two, a native realization over the io port (`120-io.md`), is
specified and not built. The document answers the dbs storage engine's
round-five request 16 (`docs/notes/oak-requests-2026-09-13.md`): a port for
the object store a storage engine offloads segments to, with the
preconditions it coordinates with.

## 1. Position

An object store is not a file system: there are no offsets, no partial
writes, no fsync. An object is a key and a value written whole, and every
successful mutation hands out a **generation**, a number the store draws
from one counter so that no two mutations of one key ever share one and a
later mutation always has the larger. Coordination happens through
**preconditions**: a put or delete names the generation it expects
(`obj_absent` for "the key must not exist", `obj_any` for "whatever it
is"), and the store applies the mutation exactly when the precondition
holds. Two writers who both read generation 7 and both put "if 7" cannot
both succeed; the loser learns the winner's generation from its failure
and decides again. This is the compare-and-set every object store offers
and the one thing a lease, a manifest, or a segment publication needs.

As with the io port, a program compiles against the port and the root
manifest's `replace objstore => objsim | objfs` selects a realization
(`83-modules.md` §4); nothing in the program text changes between a
simulation build and a native one.

## 2. Shape

Everything is caller-owned and bounded; `Memory.Allocate` never appears.
Keys and values are windows into a region the caller passes to each call,
as io buffers are.

```oak
ObjWindow: type = struct { base: u32, len: u32 }      // window into the caller's region
ObjCompletion: type = struct { generation: u64, result: u32, error: u32 }
ObjStore: type = struct { region_len: u32, objects: u32 }

obj_attach: (data: []u8, faults: u32): ()                    // sim: the tape and fault mask
obj_open_store: (store: [*]ObjStore, region: [*]u8): ()
obj_put: (store, region, key: ObjWindow, value: ObjWindow, if_generation: u64): ObjCompletion
obj_delete: (store, region, key: ObjWindow, if_generation: u64): ObjCompletion
obj_get: (store, region, key: ObjWindow, out: ObjWindow): ObjCompletion     // result: the object's size
obj_stat: (store, region, key: ObjWindow): ObjCompletion                    // generation and size, no copy
obj_list: (store, region, prefix: ObjWindow, out: ObjWindow): ObjCompletion // NUL-separated keys, result: bytes
obj_any: (): u64        obj_absent: (): u64
```

- **Keys** are one to 64 bytes whose last byte is NUL (the io port's path
  rule); **values** are at most 256 bytes in the simulation, a bound the
  native realization raises to the host's object size.
- **Preconditions.** `if_generation` is `obj_any` (always admitted),
  `obj_absent` (admitted when the key is absent), or a generation
  (admitted when the key's current generation is exactly it). A refused
  mutation completes `PreconditionFailed` with the current generation in
  `generation` — `obj_absent` when the key is absent — so a caller
  resynchronizes from the completion alone.
- **Completions.** A successful put carries the new generation and the
  value's length; a successful delete the generation it removed; `get` and
  `stat` the object's generation and size; `list` the bytes written.
- **Errors.** A closed set in `ObjCompletion.error`: `NotFound`,
  `PreconditionFailed`, `NoSpace`, `Invalid` (a window outside the region,
  a key without its NUL or over 64 bytes, a value over the bound),
  `TooLarge` (an output window smaller than the object or the listing;
  nothing is copied), `Unavailable` (the store did not answer). The
  native realization maps the host's failures onto it and keeps the raw
  code of the last failure readable.
- **No hidden work.** No realization retries on its own; a retry is a
  program decision, and a retried put must carry the precondition again.

## 3. Contract both realizations satisfy

- **Per-key linearizability.** Mutations of one key take effect in some
  total order, each observing the generation the previous one left.
- **Generations are monotone.** A successful mutation of a key hands out a
  generation strictly greater than every generation the store handed out
  before, to any key; a key deleted and re-created receives a generation
  above the deleted one. Deletion leaves the key absent (`obj_absent`).
- **Preconditions decide.** A mutation applies exactly when its
  precondition holds against the key's current generation
  (`Oak.ObjectStore.putIf_admits`); of two mutations naming the same exact
  generation, at most one applies (`putIf_exclusive`).
- **Reads see completed mutations.** A `get` or `stat` completed after a
  put's completion on the same key observes that put or a later mutation.
- **Lost acknowledgements.** A mutation whose completion is `Unavailable`
  may or may not have applied — the store answered nothing, or answered
  after applying and the answer was lost. This is the hazard the
  generation exists for: a caller that retries with its stale
  precondition is refused with the store's current generation, never
  applied twice. The simulated realization injects both faults and keeps a
  ledger of each (`objsim_unavailable`, `objsim_lost_acks`).

## 4. Simulated realization

`objsim` is pure Oak over the testing module's tape: a table of up to 16
objects, keys of 64 bytes, values of 256 bytes, one generation counter.
Every mutation rolls the tape once (one in eight rolls injects a fault
chosen uniformly among the enabled kinds): `obj_fault_unavailable` refuses
the request before anything happens, `obj_fault_lost_ack` applies the
mutation and then reports `Unavailable` with no generation. Reads roll for
`Unavailable` only. Preconditions, generations, and the listing are exact,
so a scenario's invariants — the generation a `stat` reports never goes
below one the program was told, a put admitted "if g" saw exactly g, two
puts "if g" of one key never both succeed — hold whatever the tape does
(`compiler/e2e_objstore_test.go` sweeps seeded tapes for them).

## 5. Native realization (increment two)

`objfs`, over the io port: an object is a file named by its key under the
store's directory, its generation and size in a small header the file
begins with, and a mutation is the io port's durability idiom — write the
new object under a temporary name, `fsync`, `rename` over the key,
`fsyncdir` — so that a crash leaves either the old object or the new one.
The precondition is checked by reading the current header first; the io
port's exclusive `create` realizes `obj_absent`. Because it is written over
the io port, `objfs` runs against `iosim` in a simulation build and
`ionative` in a native one, and a later realization over a network object
store's API takes the same port surface with `effects { Os.Syscall,
Network }`.

## 6. What this is not

Not a file system, not a key-value store with ranges or transactions across
keys, not versioned storage (a store keeps one value per key; the generation
is a counter, not a history), and not a cache: every completed mutation is
durable as far as the realization's device is honest.
