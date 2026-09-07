# Progress Guarantees

Concurrency folklore sorts algorithms by what they promise when threads
interfere. The ladder, weakest to strongest:

1. **Blocking** — a stalled holder can stall everyone (locks). A
   preempted or crashed lock holder in a kernel is a hang.
2. **Obstruction-free** — a thread running *alone* finishes in bounded
   steps; contention may livelock.
3. **Lock-free** — *someone* finishes in bounded steps; an individual
   thread may starve. The canonical shape is the CAS retry loop.
4. **Wait-free** — *every* thread finishes in bounded steps.
5. **Wait-free bounded / population-oblivious** — the bound is a constant
   independent of how many threads exist. The only rung with hard-realtime
   meaning.

## The Oak connection: progress bounds are loop bounds

Strip the concurrency vocabulary and every rung above is a statement about
**loop termination with a static bound** — which is exactly what Oak's
discipline profile already formalizes:

- The canonical bounded loop (`docs/spec/85-discipline.md` §3,
  `Oak.BoundedLoop`) carries a *proven static iteration bound*; every
  other `while` is flagged (`OAK-D0103`, rejected by the strict profile).
- Recursion needs a rank certificate (strict decrease on stack calls) or
  it is rejected (`OAK-D0101`); admitted tail recursion compiles to loops.

So in strict-profile Oak, an operation whose loops are all canonical and
whose atomics never retry is **wait-free bounded by construction** — the
compiler certificate *is* the progress proof. A CAS retry loop
(`while !compare_exchange(...)`) is precisely the loop the bounded-shape
analyzer refuses to certify, which makes lock-freedom syntactically
visible: rung 3 code carries an `OAK-D0103` you must consciously accept,
rung 4–5 code compiles clean under strict. Few languages give you the
ladder as a compiler diagnostic.

## Placing the standard structures

| Structure | Rung | Why |
| --- | --- | --- |
| SPSC ring (`Ring[T, N]`, one producer, one consumer) | wait-free bounded | each op is a bounded index computation + one store + one atomic index publish |
| MPSC/MPMC queue via CAS | lock-free | unbounded retry under contention (visible as the uncertified loop) |
| seqlock reader | obstruction-free | readers retry while a writer is active |
| spinlock section | blocking | the ladder's floor; in EL2 code, accept only with preemption disabled and a bound argument |
| per-CPU / custody-partitioned state | wait-free bounded, trivially | no interference exists to progress against |

The last row is the design lesson the hypervisor evaluation echoed: the
strongest progress guarantee is the one you get by **partitioning custody
so contention cannot occur** — isolation (see [Isolation](isolation.md)) bought at
design time is progress bought for free.

## Status honesty

`Atomic[T]` with C11 orderings and compare-exchange is landed on this
branch (see `docs/spec/STATUS.md`); the SPSC ring over it is expressible
today (the ring core is executed in `compiler/e2e_ring_test.go`; the
atomic index handoff composes from the atomics surface). The claim "strict
profile ⇒ wait-free bounded" holds for code whose only inter-thread
communication is single-cell atomics — the cross-thread *latency* story
(how stale a published value may be) lives in the
[memory-order ladder](../concurrency/memory-order.md), not here.
