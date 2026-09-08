# 105 — Bounded causal frontiers

Status: specified, implemented, tested, and source-refined; Lean model/proofs in
`spec/lean/Oak/CausalFrontier.lean` and source-algorithm correspondence in
`spec/lean/Oak/CausalFrontierRefinement.lean`.

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

Current ladder:

1. **specified — complete**: this chapter defines semantics, bounds, effects,
   ordering, and non-goals;
2. **modeled/proved — complete**: `Oak.CausalFrontier` proves the generic
   pointwise order and join-semilattice laws;
3. **implemented — complete**: `stdlib/causal_frontier.oak` implements bounded
   join/comparison/coverage/observe over caller-owned views/spans;
4. **tested — complete**: compiler E2E tests execute real fixed arrays natively,
   exercise error/non-mutation behavior, and reject generated heap/runtime
   dependencies;
5. **source-refined — complete**: `Oak.CausalFrontierRefinement` proves the
   executable branch expressions used by join/observe correspond to `max`, and
   that comparison/coverage correspond to the pointwise model;
6. **backend-refined — not yet complete**: there is not yet a machine-checked
   proof that arbitrary generated C preserves the Oak source semantics.

Accordingly, it is accurate to say the mathematical model and source algorithm
are formally related. It is not yet accurate to claim end-to-end formal
verification through the C backend. Native/generated-code E2E tests remain the
backend evidence until that refinement layer exists.
