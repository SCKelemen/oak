# CSP Models: Rendezvous, Channels, Mailboxes, Actors

Communicating Sequential Processes is one idea — *processes share nothing
and communicate by message* — wearing several costumes. The costumes
differ on two axes: **buffering** (does a sender wait for a receiver?) and
**addressing** (do you send to a channel or to a process?). Every one of
them is buildable from the queue structures this repository already
executes; this chapter gives the constructions and their ladder
coordinates.

## The model hierarchy

| Model | Buffering | Addressing | Blocking behavior |
| --- | --- | --- | --- |
| rendezvous (pure CSP, unbuffered channel) | none | channel | sender and receiver wait for each other |
| buffered channel (Go-style) | fixed N | channel | sender waits only when full, receiver when empty |
| mailbox | fixed N | process | senders never wait for the receiver, only for space |
| actor | fixed N | process | mailbox + the process owns all its state |

Everything below deliberately has **fixed capacity** — unbounded mailboxes
are how actor systems die in production, and Oak has no hidden allocation
to build them from anyway.

## Rendezvous: the one-slot handshake

A rendezvous is a zero-capacity channel: the transfer happens only when
both sides are present. Model the handshake as a state cell:

```oak
RVState_EMPTY: u32 = 0
RVState_OFFERED: u32 = 1
RVState_TAKEN: u32 = 2

rvState: Atomic[u32]
rvSlot: [1]u8            // written by sender, read by receiver, in place

// sender: offer, then wait for the take
// EMPTY -> OFFERED (CAS, release: publishes rvSlot)
// spin until TAKEN, then TAKEN -> EMPTY (reset)
// receiver: wait for OFFERED, read slot, OFFERED -> TAKEN (acq_rel)
```

The state machine is three CAS transitions; the payload never moves — it
is written in place, read in place, and only the *state word* is
contended. Coordinates: atomicity rung 2 (protocol over one cell),
consistency causal (release on offer, acquire on take), progress
**blocking by definition** — a rendezvous *is* mutual waiting; bound the
spins and fail-stop (`assert(tries < LIMIT)`) exactly as the
[progress chapter](../hierarchies/progress.md) demands of the floor rung.

## Buffered channel = the SPSC/zero-copy ring

A Go-style `chan T` with capacity N and one sender/one receiver is
*exactly* the executed SPSC ring (`TestE2ESpscRing`), and its zero-copy
form (`TestE2EZeroCopySpsc`) is the reserve/commit variant: full = sender
would wait, empty = receiver would wait, both conditions surfacing as
`Bool`/`Option` returns so the caller decides whether to spin, yield, or
do other work — Oak makes "blocking" a *policy at the call site*, not a
hidden property of the channel. Multi-producer channels compose the MPSC
intake in front (`TestE2EMpscIntake`); full MPMC needs per-slot sequence
counters — atomic record fields, the recorded v1 gap.

## Mailbox = MPSC, addressed to a process

A mailbox is an MPSC queue whose receiver is a fixed process. Both
executed variants apply, with different coordinates:

- **LIFO-grab** (`TestE2EMpscIntake`): lock-free senders, linearizable,
  batch-drain receiver — the general-purpose choice.
- **DV-MPSC** (`TestE2EDvMpsc`): the Vyukov queue — the sender's claim is
  one wait-free `atomic_exchange`, no retry loop at all, but the two-step
  publication (exchange, then link) opens a window in which the consumer
  observes `.Busy`: the algorithm is *blocking overall* and serializable
  rather than linearizable (int08h, ["Ode to a Vyukov
  Queue"](https://int08h.com/post/ode-to-a-vyukov-queue/)). Oak's version
  makes the window an ADT constructor — `Item | Empty | Busy` — so the
  "academically disappointing" property is a named case the receiver must
  match, not a surprise.

The choice is the ladder tradeoff in miniature: DV-MPSC buys a cheaper,
never-retrying send (better under heavy contention, and per-sender
wait-free) by selling consistency strength and consumer progress; the
grab variant buys linearizability by paying CAS retries. Neither is
"better" — they stand on different rungs, and now both stand in the test
suite.

## Actor = mailbox + custody + a behavior loop

An actor is a mailbox plus the rule that **all state behind it is owned by
the draining process** — which is Oak's custody doctrine as a programming
model:

```oak
Command: type = Deposit: u32 | Withdraw: u32 | Query

// mailbox: either MPSC variant, carrying Command values or pool indices
// state: static globals touched ONLY by the actor's own step function
actor_step: (): () {
  mailbox_pop() ?
    | .Item(cmd) => { apply(cmd) }   // plain code: rung-0, sole custody
    | .Empty => { }
    | .Busy => { }
}
```

The behavior loop is recipe 2 of [Constructing the Upper
Rungs](../structures/constructing-guarantees.md) — the operation funnel —
which is why an actor's state needs no atomics at all: the entire
concurrency budget is spent at the mailbox, and everything behind it is
single-threaded code the borrow checker fully governs. Supervision,
selective receive, and `select` over multiple channels are protocol
extensions (a select is a rendezvous race on several state cells); they
await either careful hand construction or the protocol/typestate axis.

## The FastFlow corollary: compose SPSC, avoid CAS

[FastFlow](https://github.com/fastflow/fastflow) (see also the
[1024cores notes](https://web.archive.org/web/20250719163454/https://www.1024cores.net/home/lock-free-algorithms/queues/fastflow))
demonstrates the composition doctrine at scale: build *every* topology —
fan-out farms, fan-in collectors, pipelines, feedback loops — from
**wait-free SPSC channels plus mediator processes**, and use no CAS at
all. An "MPMC queue" becomes an emitter process draining N SPSC inputs
and feeding M SPSC outputs: the sharing that forced compare-and-swap is
replaced by topology, and every hop stays on the wait-free rung. The cost
is a mediator hop of latency; the reward is that the whole network's
progress argument is just the SPSC argument repeated. In Oak terms:
`Ring[T, N]` per edge, one owning process per node, custody everywhere —
the strongest form of "reduce sharing until the protocol fits in one
atomic cell" is reducing it until the only atomics left are the ring
indices.

## The doctrine, restated

CSP's discipline and Oak's are the same discipline at two scales:
*share nothing; make the transfer point explicit; make waiting visible.*
The borrow checker enforces it within a thread of control; the queue
protocols carry it across threads; and fixed capacity everywhere keeps
every wait bounded and every failure a named case instead of a stall.
