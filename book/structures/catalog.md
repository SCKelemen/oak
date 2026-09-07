# A Catalog of Kernel Structures

Each entry names a structure, its Oak shape, and its coordinates on the
book's ladders — [atomicity](../hierarchies/atomicity.md) /
[consistency](../hierarchies/consistency.md) /
[isolation](../hierarchies/isolation.md) /
[progress](../hierarchies/progress.md). Entries marked **executed** have
end-to-end tests in this repository; the rest are expressible with today's
features unless noted.

## Ring buffer — `Ring[T, N]` — executed

```oak
Ring[T, N: u32]: type = struct {
  buffer: [N]T
  head: u32
  count: u32
}
```

`compiler/e2e_ring_test.go`. Single-owner form: atomicity rung 0 (sole
custody), progress wait-free bounded trivially. **SPSC form — executed**
(`compiler/e2e_queues_test.go`, `TestE2ESpscRing`): free-running
`Atomic[u32]` indices, plain slot writes published by
`atomic_store_release` of the producer index, consumed under
`atomic_load_acquire` — atomicity rung 2 (ownership transfer), consistency
causal, progress wait-free bounded. The kfifo/CircularQueue equivalent.

## Pool + free list

`[N]T` global plus a `next: u32` link per element and a `freeHead: u32`.
Allocation = pop, release = push; generational handles (`{index, gen}`)
upgrade use-after-free from corruption to a checked failure. Atomicity:
rung 0 under custody, rung 1 (CAS on `freeHead`) shared — which drops
progress to lock-free; per-CPU pools restore wait-free bounded.

## Intrusive doubly-linked queue — executed

The `list_head`/`IntrusiveList` replacement: index links inside pooled
elements, sentinel null. `compiler/e2e_scheduler_test.go` (enqueue,
middle unlink, dequeue). See [Intrusive
Containers](../hierarchies/intrusive.md). Single-custody: everything
trivial; shared: guard with one writer (isolation rung serializable) —
linked structures do not shard.

## Bitmap

`[N]u64` global + mask arithmetic + `arm64.clz64`/`rbit64` for scans.
Word-grain updates are atomicity rung 1 if the word is `Atomic[u64]`
(test-and-set allocation maps), rung 0 under custody. Find-first-zero
scans are bounded loops — progress wait-free bounded, and the bound is
the discipline profile's own certificate.

## Sequence lock (seqlock)

One `Atomic[u32]` version + a plain payload. Writer: bump-odd, write,
bump-even (release); reader: acquire-read version, read payload, re-check.
Atomicity rung 2 (version protocol), consistency: readers get snapshot-or
-retry, progress: writers wait-free, readers obstruction-free. The
canonical "cross-EL time struct" shape.

## MPSC mailbox — two protocols, both executed

The same job, two rungs — pick consciously:

| | LIFO-grab (`TestE2EMpscIntake`) | DV-MPSC (`TestE2EDvMpsc`) |
| --- | --- | --- |
| producer | CAS retry loop — lock-free | one `atomic_exchange` — **wait-free**, no retry ever |
| consumer | one CAS grabs the whole chain, O(batch) reversal | follows links; can observe the publication window |
| algorithm overall | lock-free | **blocking** (a stalled producer mid-publication strands the consumer) |
| consistency | linearizable (single-CAS publication) | serializable only (two-step publication can invert real-time order) |
| API honesty | `Option` empty | three states: `Item \| Empty \| Busy` — the window is a named constructor |

The DV-MPSC analysis follows int08h's ["Ode to a Vyukov
Queue"](https://int08h.com/post/ode-to-a-vyukov-queue/): academically
under-credentialed, operationally superb — the cheapest possible send
under contention. Oak's contribution is making the tradeoff visible: the
retry loop of the grab variant carries the discipline warning, and the
Vyukov window is an ADT case the consumer must match. Both are
zero-allocation and zero-copy (payloads stay pooled; indices travel).
v1 note: faithful cross-core DV-MPSC wants atomic record fields for the
links — a recorded gap. The standard inter-core doorbell; the hypervisor
design restricts it to *within one trust domain*, because a hostile
producer can spin its peers — the progress ladder is per-participant, and
adversarial participants define your floor.

## Handle table

`[N]Entry` pool + generation counters; `semir.HandleTable` carries the
generational machinery. The Zircon-koid/file-descriptor shape. Isolation:
the table is the custody root — exactly the capability-table pattern; a
lookup validates {index, gen} and yields a typed reference whose lifetime
the borrow rules bound.

## Per-CPU state

`[MAX_CPUS]PerCpu` record global indexed by CPU id: every ladder's easiest
rung by construction (no concurrent observer). Register-backed addressing
(TPIDR) awaits the assembler milestone — the indexed form is expressible
today.

## What the catalog teaches

Every entry got *cheaper to reason about* by naming its rungs, and the
recurring move is the same one: **reduce sharing until the remaining
protocol fits in one atomic cell.** The structures differ; the doctrine —
pools, typed indices, single custody, one publish point — repeats.
