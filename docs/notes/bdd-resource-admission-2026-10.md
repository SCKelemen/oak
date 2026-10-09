# BDD resource admission and cache lifetime

The verifier still uses every existing variable order, with the original
2,000,000-node default and 16,000,000-node `OAK_VERIFY_BUDGET=high` allowance.
Resource exhaustion is an undecided/evidence result, never proof. The native
Stage2 test continues to require genuine proofs of all eight named functions
and execution returning 42. Race instrumentation is unchanged.

## Disposable operation memo

The unique table is permanent for the lifetime of a diagram: canonical nodes
are never evicted. Only the operation memo is disposable. It grows at its
existing half-full threshold up to 2^22 slots (64 MiB of 16-byte entries).
At that limit the complete memo is cleared, in place, before the next insert.
A miss recomputes the exact operation against the unchanged unique table.
Whole-cache eviction preserves linear-probe chains; deleting an individual
slot would not. The constructor allocates large tables lazily, so queued
orders own only headers and their terminal node.

## Admission is an estimate, not a hard RSS limit

A process-wide FIFO admission owner covers equality, theorem and implication
order races, named-order decisions, and premise pruning. Existing candidate
orders are queued in their original order. A successful decision cancels
queued and active losers, then joins every owner. No candidate is removed
merely because another candidate temporarily owns the available reservation.
An individual request too large for the available estimate is explicitly
undecided; it is not admitted as an unbudgeted exclusive exception.

On 64-bit Go, the reservation estimate for an order with node allowance N is:

- Nodes: 2.5 × N × 24 bytes, including slice spare capacity and old/new growth.
- Unique entries: 1.5 × max(2^16, pow2ceil(2 × N)) × 16 bytes, including rehash overlap.
- Operation memo: 1.5 × 2^22 × 16 bytes, including its largest growth overlap.
- Auxiliary maps/stacks: an additional estimated 64 MiB.

This gives 370.44 MiB at two million nodes and 1,843.53 MiB at sixteen million
nodes. The default aggregate estimate is 2 GiB: up to five default orders or
one high-budget order. Race builds multiply both reservations and that limit
by three, retaining the same worst-case order concurrency while accounting
conservatively for instrumentation in host-memory admission.

The multiplier and auxiliary allowance are estimates, not measured upper
bounds. Term/blaster maps, restriction walks, stacks, uncollected older backing
arrays, compiler data and race-detector metadata are not hard-bounded by this
calculation. Neither this policy nor Go GOMEMLIMIT guarantees process RSS.
Actual process-tree RSS, completion and available host memory must be measured.

At an idle-to-active transition, admission clamps its estimate against Linux
MemAvailable and readable cgroup v1/v2 memory limits, leaving 1 GiB headroom.
The cgroup probe follows the process membership and visible ancestors, including
stricter parent groups; missing/unreadable probes retain the conservative finite
estimate limit. The capacity remains fixed while reservations are active, so
live reservations are not charged again through a falling available-memory
sample. These are observations, not guarantees of future available RAM.
Oversized numeric budgets saturate accounting and fail closed without overflow.

## Cleanup and nested work

An attempt detaches node arrays, unique entries, operation entries, the term
memo, select abstractions and owner maps before releasing its reservation.
Completed node counts survive separately, preserving the implication proof's
existing maximum-diagram budget debit. Returned results cannot borrow diagram
storage. At 64 MiB or more of released flat storage, GC/scavenging finishes
before the reservation is released. Scavenging holds no admission lock.

Ordinary admitted proof callbacks do not recursively start another blocking
order race. Recursive case splits begin only after previous orders are joined
and their stores released. Optional nested diagnostic diagrams acquire a
separate reservation without waiting, or report diagnostic exhaustion. They
must never wait for a parent reservation they themselves prevent from ending.

## Transient results and the verdict cache

A non-proof affected by memory admission must be retried when memory recovers.
`Verdict.TransientResourceExhausted` suppresses persistent cache writes and is
excluded from verdict JSON. Proven results and concrete mismatches remain
cacheable, as do deterministic negative results without a resource denial.

Because existing loop/split/pruning helpers return booleans, Verify observes an
atomic process-wide admission-denial generation across its call. A changed
generation marks only a non-Proven/non-Mismatch result transient. An unrelated
concurrent denial can conservatively cause an extra cache miss; it cannot
change acceptance or create a proof. Optional diagnostic-only denials and
ordinary winner cancellation do not increment that generation.

## Validation

Deterministic tests cover bounded memo storage and exact recomputation,
canonical-node preservation, proof/refutation/node exhaustion, all queued
orders retaining their allowances, oversized unknown results, cancellation,
FIFO admission, nested diagnostic rejection, and holding reservations through
cleanup. Other tests cover cgroup membership/ancestors and transient negative
results retrying an actual proof and remaining absent from the verdict cache.

A controlled non-race semantic probe of the unchanged Stage2 source, normal
optimizer, fresh verification and high allowance proved translate and its
trans_result state: 12,598,053 BDD nodes, 23.35 seconds of test execution,
48.78 seconds including compilation, and 2,229,817,344 bytes peak process-tree
RSS (100 ms sampling). An all-eight probe was stopped by its 2.5 GiB diagnostic
RSS watchdog after 75.35 seconds, at 2,714,656,768 bytes; it is not an all-eight
pass. Its resource trace showed HeapAlloc returning to about 34 MiB between
large attempts. This is evidence of released Go stores, not a claim that all
process RSS is Go live heap or that race metadata was reclaimed.

Local semantic probes do not execute ARM64 code. Actual native race CI and its
existing all-eight proof/reference requirements remain the acceptance check.

### Frozen candidate evidence (2026-10-09)

The implementation at `f6c45625a4dae9b701053217c62cfc93572f9f7c`, based on
`9f29884bcc8dd7af72f0a8362063f1fe25aeeb6f`, passed 53 focused race-test roots
covering the policies above, representative loops/abstract applications, and
cache serialization/retry. Total wall time including builds was 62.86 seconds;
sampled peak process-tree RSS was 1,096,302,592 bytes. Tests also distinguish
negative/zero internal node balances from memory denial: terminal-only proofs
remain possible, while a new node fails deterministically without tainting
cacheability.

A fresh all-eight semantic probe on that exact implementation passed all of
translate, unmap_page, map_page, walk_leaf, alloc_table, reset, check_range and
free_table, including their required state/span writes. It used the unchanged
Stage2 source, Linux ARM64 target, normal optimizer, InlineHelpers=true,
OAK_VERIFY_BUDGET=high and OAK_VERIFY_CACHE=0. Test runtime was 180.65 seconds
(205.79 seconds including compilation), with 2,699,624,448 bytes sampled peak
process-tree RSS and 6,288,887,808 bytes minimum available host memory. The
external diagnostic ceilings were 4 GiB RSS / 240 seconds, with 2 GiB available
memory and 512 MiB free disk floors. Neither the watchdog nor admission denied
work. The diagnostic harness does not enter the repository or replace native
execution. Log SHA-256:
`a5a741f7ac445bab6189a0dec03071828ef9d6891b8db890db4e8d7b22cda97d`.

A development-candidate race probe on the 9.7 GiB host **did not prove**
translate. It completed with explicit memory-admission-denied witness evidence:
136.48 seconds total, 4,133,797,888 bytes sampled peak RSS and 4,747,362,304 bytes
minimum available memory. No 16-million-node order ran: the 5,799,235,584-byte
race-adjusted reservation plus host headroom did not fit after the base orders.
Go HeapAlloc dropped to about 7 MiB while process RSS remained around 2.8–3.1 GB,
so the difference cannot be described as a live BDD heap. This run preceded the
classification-only correction for negative logical balances. The conservative
production thresholds were retained; hosted native/race completion is pending.

A controlled existing-node memo microbenchmark used all 32,768 canonical nodes
of the four-variable universe and 65,536 XOR operations per iteration. Across
three runs of three iterations, the growing cache retained 4 MiB and took
5.82–7.11 ms/iteration; a deliberately tiny 1 MiB cap retained 1 MiB, evicted
13 times and took 10.75–11.13 ms/iteration. Both returned every exact expected
result with the same 32,768 nodes. The small cap deliberately measures the
storage/recomputation tradeoff; the production cap remains 64 MiB. Command:

```sh
go test -p 1 -run '^$' -bench '^BenchmarkBDDOperationMemo$' -benchtime=3x -benchmem -count=3 ./asm
```

All RSS values above are sampled observations at 100 ms intervals, not hard
peak guarantees. They support hosted validation of the mitigation, not a claim
that the full native race suite has already passed.
