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
| `spsc` | 1 producer, 1 consumer | 10.1 | 9.8 | 24728 | 22.6 | 0.45× |
| `mpsc` | 4 producers, 1 consumer | 149.6 | 148.9 | 2407688 | 37.5 | 3.99× |
| `mpmc` | 4 producers, 4 consumers | 221.9 | 223.2 | 8312818 | 39.2 | 5.66× |
| `intrusive` | 4 producers, 1 consumer | 61.5 | 59.9 | 0 | — | — |

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
- **The intrusive queue's exchange is the cheaper claim**: one `swp`
  always succeeds, so four producers cost 60 ns per item where the
  compare-exchange rings cost 150–220.
- Padding the sequence cells onto their own lines (the `SeqCell` change)
  took about twenty nanoseconds off the MPSC ring and nothing off the MPMC
  ring: neighboring cells were not the problem.

## What would move the multi-producer numbers

Claiming a batch of positions per compare-exchange (one claim per
several items), the fetch-add claim of the Vyukov queue's "MPSC with
tickets" variant (an always-succeeding `amoadd`/`ldadd`, as the intrusive
queue's exchange), and core pinning in the harness. Each is a design
change to be measured here before it is adopted.
