# The Atomicity Hierarchy

Atomicity answers one question: **what can be observed half-done?** The
ladder runs from "everything" to "nothing", and hardware only sells the
bottom rungs — everything above is protocol.

## Rung 0 — no atomicity

Plain memory accesses. Under concurrency, another observer may see a torn
write (on some widths/alignments), a partial structure, or any
interleaving. Legal only where no concurrent observer exists — which is a
*custody* claim, not a memory claim. Oak's contribution: custody is
something the borrow checker and the design (single-owner state, per-CPU
partitioning) can make true, instead of something a comment asserts.

## Rung 1 — single machine word

The hardware rung. `Atomic[T]` cells over fixed-width carriers give
indivisible loads, stores, and read-modify-writes (add, exchange,
compare-exchange) on exactly one word. Oak makes the rung a **storage
identity**: `Atomic[T]` cannot be embedded in ordinary record values, read
by assignment, or matched — only the explicit `atomic_*` operations touch
it, each naming its [memory order](../concurrency/memory-order.md).
Lowering is C11 `_Atomic`; order/operation legality is proven
(`Oak.MemoryOrder`); host lock-freedom is verified in the test suite.

Everything indivisible at this rung is one word. A 16-byte "atomic"
structure is rung-2 fiction unless the ISA provides it and the language
exposes it — Oak does not pretend.

## Rung 2 — single-object protocols

Multi-word atomicity is constructed from rung 1 plus ordering:

- **ownership transfer** — SPSC ring handoff: the producer fills a slot
  (plain writes, rung 0, sole custody), then *publishes* it with one
  release store of the index; indivisibility comes from the fact that
  custody changes hands exactly once, at the publish.
- **version counters** — seqlock: writers bump an odd/even counter around
  the update; readers retry on torn observation. Observable half-done, but
  *detectably* so.
- **exclusive custody** — the object is only ever touched by one core /
  one exception level; atomicity is vacuous. The strongest protocol is
  the one that removes the observer.

Oak expresses these as ordinary code over `Atomic[T]` + records; the
[progress ladder](progress.md) classifies what each costs under
contention.

## Rung 3 — multi-object transactions

Not a language feature, and never will be: transactional semantics over
arbitrary memory is either speculative hardware (fragile, niche) or a
database engine (a program, not a primitive). Oak's stance is the
TigerStyle one — design state machines whose steps are rung-1 or rung-2
operations, so "transaction" becomes a sequence of individually
indivisible steps with explicit intermediate states, each one an ADT
constructor a `?` match must handle. The intermediate states get *names*,
which is what makes crash-recovery reasoning (see
[Durability](durability.md)) tractable.

## The rule

State the rung in the design, then check the code stands on it:
rung 0 requires a custody argument (increasingly, a borrow-checker fact);
rung 1 requires an `Atomic[T]` cell; rung 2 requires a named protocol with
its publish points identified; rung 3 requires you to admit you are
building a database and to write down its state machine.
