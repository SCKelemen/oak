# SPSC batch safety and OS adoption gate

This note clarifies the low-level `rings` API in
[`65-machine-memory.md`](../spec/65-machine-memory.md), following PR #628.
It is not a claim that the ring is already a sealed, linear endpoint type.

## Consumer cache invariant

The consumer owns both `head` and its plain `tail_seen` cache. In lifted logical
positions, `head <= tail_seen <= published_tail`. Scalar pop relies on equality
with `tail_seen` to decide when another acquire is needed.

Bulk consume must refresh `tail_seen` from the acquired tail before releasing
its new head. Updating only head can skip beyond the scalar cache: a later pop
then reports an item even though the queue is empty. This is a safety defect,
not merely a stale performance hint. Both cold-cache and warm-cache mixes need
regression coverage.

Successful `consume(n)` therefore performs:

1. Load head and acquire the current published tail.
2. Reject `n > tail - head` without changing either consumer field.
3. Set `tail_seen = tail` and release `head + n`.

`consume(0)` is permitted and may refresh the private cache without releasing
any new slots. The operations themselves do not sleep, allocate, or retry.

## Producer reservation lifecycle

`SpscProducerBatch` is producer-private state, not part of the shared cursor.
It records the starting tail, capacity, reserved count, and written count.
The shared `SpscCursor` layout is unchanged.

- `reserve(n)` replaces an unpublished reservation. An invalid size or lack of
  room leaves it inactive and does not publish data.
- `put_run` accepts at most the remaining reserved count. It refuses an inactive
  or stale-tail batch, a different capacity, or inconsistent counts before
  writing payload. Filling is O(accepted items), bounded by capacity.
- `commit(n)` requires a current reservation and `n <= filled <= reserved`.
  It publishes a written prefix with one release store and clears the batch.
  Partial commit abandons the suffix. `commit(0)` abandons the whole batch.
- A refused commit publishes nothing. A second commit after success is refused.
- Do not mix scalar producer operations into an open batch. The saved-tail
  check detects an ordinary intervening scalar push; it is defensive validation,
  not permission to share or concurrently mutate producer state.

The caller must keep exactly one producer and one consumer per SPSC instance.
An outstanding batch must not be copied, forged, rebound, or retained across
reset or a full counter cycle. Equal capacity and tail are not ring identity.
The public record is not yet a generative/noncopyable reservation capability.

## Zero-copy receive and remaining authority boundary

`run()` returns a borrowed read-only view of the first contiguous published
range. It does not consume it. A fixed captured queue prefix fits in at most
two physical runs; a concurrently replenished queue can take arbitrarily many
calls to drain, so callers must choose a bounded drain budget for realtime work.

End the view's scope before `consume()` reacquires a writable span of the same
payload storage. Oak's checked borrow boundary prevents that same-storage
reacquisition while the view lives. It does not prove that an independently
supplied cursor and storage are the correct pair, nor validate raw FFI aliases.
Those remain caller/adapter obligations until an opaque producer/consumer
endpoint owns the pairing and the reservation lifecycle.

The acquire of published tail orders prior producer writes before reads of the
run. The release of consumed head and the producer's acquire order those reads
before reuse. Notifications are separate and carry no payload authority.
`spsc_count` is advisory under concurrency and must not authorize payload access.

## Verification and adoption

`compiler/e2e_rings_batch_regression_test.go` exercises the actual Oak library
through interpretation and compiled C execution. It covers mixed scalar/bulk
consumption, full/empty refusal, unpublished data, partial/zero/double commit,
reservation replacement, stale-tail rejection, shape mismatch, physical wrap,
and u32 counter rollover. The existing negative borrow test remains required.
The existing threaded tests provide separate concurrent publication coverage;
sequential API tests do not establish an ARM weak-memory proof.

`Oak.Rings` contains abstract FIFO, wrapping, and release/acquire facts. The new
`consumeN_wf`, `consumeN_inv`, `consume_cache_valid`, and
`consume_all_cache_empty` lemmas describe the abstract consumption/cache model.
The contiguous-run bounds use explicit `Nat.min_le_left/right` proofs rather
than assuming `simp` will discharge them. These are model theorems, not a complete
compiler-to-machine refinement of the batch implementation.

The focused **SPSC ring safety** workflow runs ring tests and the Lean ring
module independently of the long general CI shards. Passing it does not replace
full compiler CI or OS integration/performance testing.

Before advancing the OS compiler pin or deleting its local ring implementation:

1. Require the relevant runtime, negative borrow, Lean, and general compiler
   gates to pass on the exact candidate revision.
2. Run the OS differential/performance harness against the shared package.
3. Audit its ABI: the upstream cursor uses u32 positions; the older OS ring uses
   u64 positions. Do not reinterpret one layout as the other.
4. Re-run native AArch64, QEMU, and Linux shared-memory tests with regenerated
   artifacts before changing production ownership.

This corrective slice does not implement generic custody buffers, sealed
endpoints, or change MPSC/MPMC algorithms or their progress semantics.
