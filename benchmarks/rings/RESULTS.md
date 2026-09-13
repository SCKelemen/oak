# Rings benchmark results

## Baseline, 2026-09-13

Measured Oak revision: `b20a56661ca20a24d5bf221d339846809b2bed64` plus the `SeqCell` layout of this
change (one sequence cell per 64-byte line). Apple M4 Max, macOS 26.3.1,
Apple clang 21.0.0 `-O2`, Go 1.27.1; two million items per transfer,
capacity 1024, five samples, medians, cores not pinned and the machine
running other test suites. Raw data:
[rings-2026-09-13-m4max.json](rings-2026-09-13-m4max.json).

| Ring | Threads | Oak spin ns/item | Oak yield ns/item | producer spins (spin) | Go channel ns/item | Oak spin / Go |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `spsc` | 1 producer, 1 consumer | 8.8 | 9.7 | 5729 | 24.7 | 0.36× |
| `mpsc` | 4 producers, 1 consumer | 126.3 | 136.0 | 0 | 35.8 | 3.53× |
| `mpsc_ticket` | 4 producers, 1 consumer | 72.8 | 75.4 | 0 | 35.8 | 2.03× |
| `mpmc` | 4 producers, 4 consumers | 217.5 | 211.5 | 14036242 | 36.7 | 5.93× |
| `mpmc_ticket` | 4 producers, 4 consumers | 99.7 | 104.2 | 10878719 | 36.7 | 2.72× |
| `intrusive` | 4 producers, 1 consumer | 49.0 | 56.1 | 0 | — | — |

"Spin" is the Oak producer loop retrying a refused push at once; "yield" is
a C loop calling the same push and `sched_yield()` when the ring is full.
The Go reference is a buffered `chan uint32` of the same capacity between
the same threads.

## Reading the table

- **SPSC** costs about 10 ns per item end to end — two release/acquire
  handoffs and the cached opposite index — and beats the Go channel by
  more than two to one, since the channel takes a mutex per operation.
- **The multi-producer rings are contention-bound, not spin-bound.** With
  one producer the same code moves an item through the MPSC ring in about
  22 ns, through the MPMC ring in under 8 ns, and through the intrusive
  queue in about 7 ns (measured with `-DP=1`, not tabulated). At four
  producers every claim is a compare-exchange on one cache line contended
  by four cores, and each failed claim re-reads a slot's sequence cell
  another core is publishing. Yielding on a full ring changes nothing,
  which confirms the cost is the claim, not the wait. The Go channel's
  mutex serializes producers cheaply at this saturation and parks them.
- **Tickets are the cheaper claim.** `mpsc_ticket` and `mpmc_ticket` claim
  by fetch-add — one `ldadd` that always succeeds — and then wait for the
  slot: they move an item in roughly half the time of the compare-exchange
  rings at four producers, with or without yielding while a publish waits
  (the wait is short: the consumer is a few slots behind). The price is the
  ticket's obligation: a claimed position must be published or taken, so
  the application decides how to wait. The intrusive queue's
  exchange is the same idea for a linked queue.
- Padding the sequence cells onto their own lines (the `SeqCell` change)
  took about twenty nanoseconds off the MPSC ring and nothing off the MPMC
  ring: neighboring cells were not the problem.

## What would move the multi-producer numbers further

Claiming a batch of positions per fetch-add (one claim per several items)
and core pinning in the harness; each to be measured here before it is
adopted.
