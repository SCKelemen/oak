# The Isolation Hierarchy

Isolation answers: **while I work with this state, what may others do to
it?** Databases named the rungs; Oak's claim is that the borrow checker is
a *static* isolation-level scheduler, deciding at compile time what a lock
manager decides at run time.

## The ladder

1. **Read uncommitted** — observers may see in-progress writes: dirty
   reads, torn invariants.
2. **Read committed** — only completed writes are visible, but two reads
   in one scope may disagree (non-repeatable reads).
3. **Repeatable read / snapshot** — a scope's reads are stable; write
   skew between scopes remains possible.
4. **Serializable** — the outcome of executing concurrent transactions is
   **equal to the outcome of executing the same transactions one at a
   time in some serial order**. The order may be any order — including one
   that contradicts real time — and the guarantee covers whole
   transactions, not single operations. With predicate/range locking the
   equivalence extends to the *sets* a transaction read, excluding
   phantoms (rows appearing mid-transaction in a range already read).
5. **Strict serializable** — serializable **and** the equivalent serial
   order respects real time: if transaction A committed before B began, A
   precedes B in it. This is [linearizability](consistency.md) lifted from
   single operations on one object to transactions over many.

## The borrow checker as the scheduler

Read "transaction" as "borrow lifetime over a place":

| Rung | Oak mechanism |
| --- | --- |
| serializable (exclusive) | a writable span `[*]T`: one writer, zero readers, enforced at compile time (`OAK-B0102`..`B0105`) |
| snapshot / repeatable read | read-only views `[]T`: any number of readers, writers excluded while any is live |
| range / predicate locks | **region-disjoint sibling spans**: two writers coexist iff their element regions are *statically proven* disjoint — `Oak.Reborrow.Split` proves admission requires pairwise disjointness, and `Oak.ReborrowRefinement` proves the compiler's decision procedure sound and complete against it. Unknown regions fail closed (`OAK-B0106`/`B0107`) |
| read uncommitted | the `unsafe` boundary: the *only* admissible relaxation is unproven writable disjointness, and each admission is recorded as an auditable `OAK-B0110` warning — dirty is legal solely as a signed declaration |

Two properties databases cannot offer:

- **Zero runtime cost.** The schedule is decided per compilation; there is
  no lock word, no waiting, no deadlock — conflicting programs are
  rejected, not queued.
- **No escape.** `OAK-B0109` forbids returning views/spans: no "borrow"
  outlives its scope, so there is no analogue of a transaction handle
  leaking past commit.

## Isolation across cores and exception levels

The borrow checker schedules within one thread of control. Across cores,
isolation is bought structurally — custody partitioning (per-CPU state,
single-owner objects, an EL2 core owning all custody state), with
cross-boundary communication demoted to explicit protocol over `Atomic[T]`
(see [Atomicity](atomicity.md) rung 2). The design rule mirrors the
database one: the cheapest serializable system is the one whose
transactions never touch shared rows. Typestate/session-typed protocols
(the `docs/spec/` protocol axis, still direction) are the recorded path to
making cross-boundary isolation as checkable as the intra-thread kind.

Serializable and strict-serializable *transactions* are not language
features; they are built — single-sequencer executors, deterministic
partitioning, and (as a last resort) lock tables — with recipes and their
proof obligations in
[Constructing the Upper Rungs](../structures/constructing-guarantees.md).
