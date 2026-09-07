# Constructing the Upper Rungs

Oak deliberately does not ship linearizable objects or serializable
transactions as language features — the [atomicity
ladder](../hierarchies/atomicity.md) ends at the single cell, on purpose.
This chapter is for the people building the things above the language:
databases, kernels, hypervisors, storage engines. Each recipe names its
**linearization or serialization point**, its ladder coordinates, and what
remains for you to check — because a constructed guarantee is a proof
obligation, and the honest recipe says where the obligation lives.

The primitives every recipe is built from: `Atomic[T]` cells with
`atomic_load_acquire` / `atomic_store_release` / `atomic_fetch_add_*` /
`atomic_compare_exchange_<success>_<failure>`, pools with typed index
links, custody partitioning, and bounded loops.

## Recipe 1 — a linearizable multi-word object: build-then-publish

The fundamental move: **make the object immutable, and linearize the
pointer.** In Oak, "pointer" is an index into a pool.

```oak
Config: type = struct {
  timeoutMs: u32
  retries: u32
}

slots: [2]Config
current: Atomic[u32]     // index of the live slot

// Writer (single writer by custody):
//   build the NEW slot completely with plain writes (rung-0: sole custody
//   of the non-live slot), then publish with ONE release store.
publish: (next: u32): () {
  atomic_store_release(current, next)   // <- the linearization point
}

// Reader, any core:
read_timeout: (): u32 {
  slots[atomic_load_acquire(current)].timeoutMs
}
```

Why it is linearizable: every read and write of the *object* takes effect
at the instant of exactly one atomic operation on `current`, whose per-cell
history is linearizable by hardware. Acquire/release makes the slot's
plain writes visible before the index that names them
([causal rung](../hierarchies/consistency.md)) — publish without release
is the classic bug this recipe exists to prevent.

Obligations left to you: single-writer custody of the spare slot; readers
must not cache the index across a "transaction" (re-read per operation).
Generalize slots with a generation counter when writers are frequent
(RCU-shaped reclamation: a slot is reusable when no reader can still hold
its index — in bounded-interrupt kernel contexts, "after the next
quiescent point").

## Recipe 2 — a linearizable arbitrary object: the operation funnel

When the object cannot be immutable-swapped (a B-tree page cache, a wait
queue), serialize the *operations* instead of the data:

```
producers ──MPSC mailbox──▶ single executor core owns the object
```

Producers enqueue operation records (an ADT: one constructor per
operation) into a mailbox; one executor dequeues and applies them with
plain code — no locks, no shared mutation. **Linearization point: the
mailbox's publish** (the `atomic_fetch_add`/CAS that claims the slot plus
the release store that completes it). Responses return by per-producer
reply slots or completion indices.

Executed: `compiler/e2e_queues_test.go` runs both halves of this recipe —
the SPSC ring (`TestE2ESpscRing`) and the MPSC intake with LIFO-grab and
in-place FIFO reversal (`TestE2EMpscIntake`).
Coordinates: object code is rung-0 (sole custody) — the entire concurrency
budget is spent inside one mailbox. Progress: producers lock-free (CAS
claim) or wait-free (fetch_add claim with bounded slots); executor
wait-free bounded. This is also the recipe's deeper lesson: *a
linearizable object is a tiny single-threaded database*, and the mailbox
is its log.

## Recipe 3 — serializable (indeed strict serializable) transactions:
## the single-sequencer design

The database version of Recipe 2, and the TigerBeetle answer: **the
cheapest serializable executor is a serial one.**

1. **Sequence**: all transactions pass one point that assigns positions —
   a single `atomic_fetch_add_acq_rel` on a sequence cell, or one core
   that owns intake. The serial order *is* the sequence.
2. **Execute** in sequence order on one core (or deterministically
   partitioned cores — step 3). Because execution follows the commit
   order, the result is not just serializable but **strict serializable**:
   the serial order respects real time by construction, since sequencing
   happens inside each transaction's invocation window.
3. **Partition** for scale: shard state by key so most transactions touch
   one shard (custody = [isolation](../hierarchies/isolation.md) bought
   structurally); cross-shard transactions execute in sequence order on
   every shard they touch (Calvin-style deterministic execution) — the
   sequence decided *before* execution is what keeps the shards agreeing
   without two-phase commit's blocking.

Serialization point: the fetch_add. Obligations: transactions must be
deterministic (no wall-clock, no allocation surprises — Oak's discipline
profile is doing real work here) and bounded (a transaction is a bounded
loop over bounded state; `OAK-D0103`-clean code gives the executor a
latency bound). Durability composes in by writing the sequence log through
the [durability ladder](../hierarchies/durability.md) *before* execution
acknowledges.

## Recipe 4 — pessimistic locking, when you truly need it

Dynamic transactions over dynamically-chosen rows sometimes defeat static
custody. The lock table is then an array of `Atomic[u32]` words: acquire =
`atomic_compare_exchange_acquire_relaxed` from 0 to owner-id; release =
`atomic_store_release(0)`. Two-phase discipline (acquire all, then
release all) gives serializability; ordered acquisition (by lock index)
gives deadlock freedom; a bounded spin with fail-stop
(`assert(tries < LIMIT)`) keeps the [progress
floor](../hierarchies/progress.md) honest instead of silent. This recipe
is listed last deliberately: it is the one whose obligations (every
access covered by its lock; no escape of borrowed state past release) Oak
cannot yet see — prefer Recipes 1–3, which put the obligation into one
atomic cell the type system already quarantines.

## What to check, and where

Constructed guarantees deserve constructed checks, in increasing strength:
**assert the invariants** at every publish/claim point (never elided);
**test destructively** — deterministic simulation with fault injection is
viable precisely because Oak code is allocation-free and bounded;
**model-check the protocol** — the recipes above are a few dozen lines of
TLA⁺/PlusCal each, and the linearization/serialization points named here
are exactly the atomic actions the model's next-state relation should
contain. The language's future protocol/typestate axis is reserved for
pulling some of these obligations into the checker; until then, the recipe
card states them, and your test rig enforces them.
