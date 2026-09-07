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
custody), progress wait-free bounded trivially. SPSC form: indices become
`Atomic[u32]` with release-publish/acquire-consume — atomicity rung 2
(ownership transfer), consistency causal, progress wait-free bounded.
The kfifo/CircularQueue equivalent.

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

## MPSC mailbox

Producers CAS a slot claim (lock-free), single consumer drains custody
(wait-free). The standard inter-core doorbell; the pattern the hypervisor
design restricts to *within one trust domain*, because a hostile producer
can spin its peers — the progress ladder is per-participant, and adversarial
participants define your floor.

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
