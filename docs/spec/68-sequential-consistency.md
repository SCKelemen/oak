# Sequential consistency: one explicit global order

This chapter closes the language-level `seq-cst` ordering contract above the
execution, happens-before, modification-order, release-sequence, and fence
relations defined in chapters 66 and 67.

The governing rule is:

> `seq-cst` is a single global ordering constraint, not merely a stronger local
> acquire/release annotation.

## 1. The SC witness

Every execution that contains seq-cst events may be paired with a
`SequentialConsistencyWitness`:

```text
S = [event_0, event_1, ... event_n]
```

Position in `S` is the event's global SC rank.

`S` is deliberately separate from `MemoryEvent`. Program order, reads-from,
modification order, happens-before, and global SC order remain distinct facts.

The witness is caller-owned. The reference verifier does not allocate an
internal list, tree, or map to construct it.

## 2. Exact membership

The witness must contain:

- every seq-cst event in the execution;
- only seq-cst events;
- every such event exactly once.

A concrete list with exact membership gives a strict total order by
construction. No pairwise Boolean order matrix is stored.

The reference implementation uses bounded linear position lookup. That is
intentional: the verification model values auditability and zero hidden
allocation over premature indexing. An optimized index may later refine this
representation if measurements justify it.

## 3. Happens-before consistency

For seq-cst events `A` and `B`:

```text
A happens-before B
    =>
A SC-before B
```

Therefore the global SC order may never reverse an established happens-before
edge.

This includes same-thread sequenced-before because sequenced-before is one of
the generators of happens-before.

## 4. Modification-order consistency

For seq-cst write-like events `A` and `B` to the same atomic location:

```text
A modification-before B
    =>
A SC-before B
```

Thus one location cannot appear to move backward merely because the global SC
witness chose a different order.

This constraint is independent of HB: concurrent seq-cst writes still have a
per-location modification order that the global order must respect.

## 5. SC read visibility

A global order that ignores observed values is insufficient. Oak therefore
validates the source of every seq-cst read or read-modify-write.

Suppose seq-cst read `R` reads-from modification `W`.

### 5.1 Seq-cst source

If `W` itself is seq-cst:

```text
W SC-before R
```

must hold.

An SC read cannot observe an SC write that globally occurs after the read.

### 5.2 Later visible modifications

For every modification `L` later than `W` on the same location, the execution
is rejected if either is true:

```text
L happens-before R
```

or:

```text
L is seq-cst
&& L SC-before R
```

In other words, `R` may not skip a later modification that is already visible
before it through the language's causal or global SC relations.

This allows a seq-cst read to observe a concurrent non-SC write when no later
write is already visible before the read. Oak therefore does not falsely imply
that seq-cst operations exclude all interaction with weaker atomics.

### 5.3 Implicit initialized value

A seq-cst read with no represented reads-from source observes the location's
implicit initialized value.

That is valid only if there is no represented write to the location that is
already visible before the read through HB or, for a seq-cst write, through the
SC order.

Thus an initial-value read cannot pretend a known prior write did not happen.

## 6. RMW interaction

Chapter 67 already requires an RMW at modification `n > 0` to read-from the
immediately preceding modification `n - 1`.

For a seq-cst RMW, both contracts apply:

- the RMW source is fixed by immediate modification-order predecessor;
- the RMW itself appears exactly once in global SC order;
- if the source is seq-cst, the source is SC-before the RMW;
- the global order may not reverse HB or modification order.

This avoids giving CAS/fetch-add a separate ad-hoc SC model.

## 7. Fences

Seq-cst fences participate in the same global SC witness even though they do not
name a memory location or occupy modification order.

Their relative placement is constrained by HB just like every other seq-cst
event. The release/acquire synchronization paths that produce those HB edges
remain the explicit witness rules from chapter 67.

The SC witness does not invent fence synchronization by itself.

## 8. Allocation and bounded-work contract

`ValidateSequentialConsistency` is verification/tooling machinery, not a hidden
runtime service.

Its success path obeys:

1. the SC order slice is caller-owned;
2. HB scratch is caller-owned and reused;
3. no hash map, balanced tree, linked list, recursive walk, or heap-backed queue
   is constructed;
4. membership and position queries are bounded linear scans;
5. HB/MO/visibility validation uses bounded nested scans over the finite
   execution;
6. zero internal allocations are regression-tested with
   `testing.AllocsPerRun`.

The current verifier intentionally accepts higher asymptotic verification cost
in exchange for an extremely small, deterministic implementation. It is not on
the OS runtime hot path. If large trace verification later requires indexing,
the optimized implementation must refine the same semantics and retain an
explicit allocation budget.

## 9. Formal verification

`spec/lean/Oak/SequentialConsistency.lean` defines an abstract strict total
order over seq-cst events and formalizes:

- consistency of SC order with happens-before;
- consistency of SC order with modification order for seq-cst writes;
- visibility of the write source observed by an SC read;
- the rule forbidding a later HB-visible modification from being skipped;
- the rule forbidding a later seq-cst modification already SC-before the read
  from being skipped;
- the rule that an observed seq-cst source must be SC-before its read;
- the rule that an initial-value SC read cannot have a seq-cst write already
  SC-before it.

Lean proves that an HB-consistent SC order cannot reverse HB and that an
MO-consistent SC order cannot reverse per-location modification order.

As with the earlier memory-model chapters, these are mathematical language
proofs. A direct Go-to-Lean refinement proof remains separate work.

## 10. Executable tests

The Semantic IR tests cover:

- a valid seq-cst release/acquire publication;
- rejection when global SC order reverses HB;
- rejection when global SC order reverses modification order;
- rejection when an SC read skips a later SC write already before it in S;
- acceptance of an SC read observing a concurrent non-SC write;
- rejection when such a non-SC source is followed by a later SC write already
  SC-before the read;
- rejection of an initial-value SC read after a visible write;
- acceptance of an initial-value SC read with no visible write;
- exact witness membership: missing, duplicate, and non-SC entries fail;
- explicit caller-workspace failure;
- zero-allocation validation on a valid execution.

## 11. Verification status

| Layer | Status |
| --- | --- |
| explicit global SC witness | specified + implemented |
| exact SC-event membership | specified + implemented + tested |
| SC/HB consistency | specified + implemented + Lean-modeled |
| SC/modification-order consistency | specified + implemented + Lean-modeled |
| SC source visibility | specified + implemented + Lean-modeled |
| implicit-initial SC visibility | specified + implemented + Lean-modeled |
| zero-allocation SC validation | regression-tested |
| implementation-to-Lean refinement | not yet proved |
| compiler/C weak-memory refinement | next major layer |
| AArch64 assembly/litmus validation | next major layer |
| target lock-free admission | not yet implemented |

## 12. Language-level memory model closure

With chapters 65 through 68, Oak has explicit language-level definitions for:

```text
atomic operation legality
reads-from
sequenced-before
per-location modification order
release sequences
fence synchronization
synchronizes-with
happens-before
conflicting accesses
data races
global sequential consistency
SC read visibility
```

That is enough to stop inventing new language semantics when implementing the
backend.

The next work is **refinement**: demonstrate that generated C and AArch64 code
preserve these relations with litmus tests, assembly inspection, and eventually
formal refinement where practical. Only after that should a lock-free queue be
accepted as relying on Oak's memory model end to end.
