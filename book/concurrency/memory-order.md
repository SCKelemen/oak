# The Memory-Order Ladder

Two cores disagree about the order of events unless you pay for
agreement. The ladder below is ordered by how much agreement each rung
buys; the engineering discipline is to stand on the *lowest* rung that
makes your invariant hold, because every rung above it costs cycles on
every operation.

1. **Plain accesses** — no inter-thread ordering at all. Legal only for
   data-race-free use: thread-local state, custody-partitioned state, or
   data protected by a rung above. Oak's aliasing rules make the
   single-thread story sound; across threads, plain access to shared
   mutable state is the bug.
2. **Volatile / MMIO** — ordering against the *device*, not other cores.
   Oak's typed MMIO surface (`arm64.mmio_*`, chapter 69 family) makes
   device access a distinct operation that the compiler may not merge,
   elide, or reorder; it deliberately provides no inter-core guarantee.
   On non-AArch64 targets the lowering fails closed rather than
   pretending (`#error`, tested host-independently).
3. **Relaxed atomics** — indivisibility without ordering: counters,
   statistics, generation stamps whose readers tolerate staleness.
4. **Acquire / release** — the workhorse rung: a release store publishes
   everything sequenced before it to the acquire load that reads it.
   Ring-buffer index publication lives here — release on the producer's
   index store, acquire on the consumer's load.
5. **Sequentially consistent** — one global order of all seq_cst
   operations. Needed rarely (Dekker-style mutual inspection); expensive
   always. Treat as a design smell to justify, not a default.
6. **Barriers** (`dmb`/`dsb`/`isb`) — the instruction-level substrate:
   ordering statements about *all* prior/subsequent accesses of a class,
   for the places C11's object-level model cannot reach (MMIO ordering
   against normal memory, context synchronization after sysreg writes,
   pre-DMA cleanup).

## Oak's implementation of the ladder

`Atomic[T]` is a storage identity, not a value type: it cannot be
embedded in ordinary records, read, or matched — only operated on through
explicit `atomic_*` operations that name their order. The legality of
order/operation pairs is proven (`Oak.MemoryOrder`), lowering is C11
`_Atomic` with host lock-freedom verified, and the AArch64 mapping is
covered by the memory-model refinement and litmus work recorded in
`docs/spec/STATUS.md`. Barriers and MMIO are `arm64.*` instruction
functions: total at the interface, real instructions on target,
fail-closed elsewhere — never a fake portable semantics for something
that has none.

## Choosing a rung: the three questions

1. **Who else touches this place?** Nobody concurrent → rung 1 and stop.
   This is why custody partitioning (see [Isolation](../hierarchies/isolation.md))
   is the highest-leverage concurrency decision.
2. **Is the value itself the message, or a flag for other memory?** Value
   only → rung 3. Flag/index publishing a payload → rung 4, release on
   write, acquire on read.
3. **Is a device or another exception level watching?** Then object-level
   orders are insufficient by definition — rung 2 for the access, rung 6
   for its ordering against everything else.

The [progress ladder](../hierarchies/progress.md) and this one compose at
right angles: a wait-free algorithm at the wrong memory order is wrong
fast; a seq_cst algorithm that could be acquire/release is correct
slowly. Kernel code gets to be wrong on neither axis.
