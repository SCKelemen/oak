# 105 — Bounded causal frontiers

Status: specified; Lean model/proofs in `spec/lean/Oak/CausalFrontier.lean`.

## Purpose

Oak needs one small reusable causal-context primitive that can serve systems
software without imposing a database, scheduler, tracing, or distributed
runtime policy. The motivating consumers are:

- OS structured-event causality, synchronization edges, replay, and debugger
  reconstruction;
- database replication, CRDT convergence, and event/log causal context.

A causal frontier is not a global clock and does not manufacture a total order.
It records only the strongest known per-actor prefix.

## Semantic model

For a compile-time actor count `N`, a frontier is a fixed contiguous vector of
`N` monotonically increasing unsigned counters:

```
Frontier[N] = [N]Counter
EventId     = { actor : ActorId[N], seq : Counter }
```

The mathematical model uses `Fin N -> Nat`, making an out-of-range actor
unrepresentable.

Pointwise causal domination is:

```
a <= b  iff  for every actor i, a[i] <= b[i]
```

The empty history is the all-zero vector.

Merge is pointwise maximum:

```
join(a, b)[i] = max(a[i], b[i])
```

A frontier covers a dot `(actor, seq)` when:

```
seq <= frontier[actor]
```

## Required laws

`join` is the least-upper-bound operation of a bounded join-semilattice:

- idempotent: `join(a, a) = a`;
- commutative: `join(a, b) = join(b, a)`;
- associative;
- bottom identity;
- `a <= join(a, b)` and `b <= join(a, b)`;
- if `a <= upper` and `b <= upper`, then `join(a, b) <= upper`;
- merge is monotone in both arguments;
- merge never forgets an already-covered event dot.

These laws are mechanically checked in Lean.

## Representation and performance contract

The executable representation MUST be statically bounded and contiguous.
Version 1 permits only a compile-time capacity; it MUST NOT allocate, resize,
use a map, hash table, linked structure, callback, or hidden runtime descriptor.

A join performs exactly one bounded pass over `N` counters and writes at most
`N` counters. An observe operation touches one actor counter. Overflow MUST be
explicitly handled; wrapping a causal counter is not valid semantics.

The language/runtime MUST NOT attach a full frontier to every event by default.
A preferred systems representation is a compact event dot plus explicit
frontier merge/capture at synchronization boundaries. This avoids turning
causality into a global hot-path tax.

## Ordering

A frontier defines a partial order only. Concurrent frontiers are valid and
must remain distinguishable as concurrent. Display/debugger code may apply a
deterministic tie-breaker, but that tie-breaker is not a happens-before edge.

This primitive is independent of physical/wall clocks. In particular, database
commit-wait policies and externally consistent timestamp assignment remain
application/protocol policy rather than frontier semantics.

## Authority and effects

Pure operations (`join`, comparison, coverage) have no effects. Mutable
`observe`/`joinInto` style operations may write only the caller-provided
frontier storage and must expose that mutation through Oak's ordinary borrowing
rules. They perform no allocation, blocking, I/O, atomics, or synchronization
unless a future explicitly concurrent wrapper states otherwise.

## Verification maturity

Current intended ladder:

1. **specified** — this chapter;
2. **modeled/proved** — generic Lean frontier and semilattice laws;
3. **implemented** — fixed-capacity Oak source representation using existing
   array/borrowing constructs;
4. **tested** — executable merge/coverage/observe tests plus allocation/cost
   regression checks;
5. **refined** — explicit correspondence between the executable operations and
   the Lean pointwise model.

Do not call an executable frontier formally verified until the refinement step
exists. The Lean laws prove the mathematical model, not arbitrary generated
code by themselves.
