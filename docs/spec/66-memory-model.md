# Memory model: executions, happens-before, and data races

This chapter defines the execution-graph core beneath Oak concurrency. It is the
semantic bridge between source-level atomic operations and higher-level queues,
channels, schedulers, device protocols, and realtime code.

The governing rule is:

> Shared-memory correctness is an explicit relation between events, not an
> accidental consequence of compiler or processor behavior.

This chapter intentionally separates two questions:

1. **What is happens-before and what constitutes a data race?** This chapter
   specifies and implements those core relations.
2. **Which synchronization witnesses are valid?** `67-memory-ordering.md`
   extends the same execution model with modification order, release sequences,
   and fence-mediated synchronization. Sequential consistency, backend
   refinement, and AArch64 litmus validation remain closure work before the
   complete machine memory model is declared finished.

## 1. Execution events

A memory-model execution is a finite set of indexed events. Event identity is a
compact integer index rather than a pointer or heap object.

The core event vocabulary carries:

```text
thread
sequence
location
access       // read, write, read-write, or fence
atomic
order        // only for atomic events
reads_from?  // only for atomic reads/RMW
```

Chapter 67 extends write-like atomic events with explicit per-location
modification-order indices while preserving these identities and relations.

`location` is semantic storage identity. It is not required to be a virtual or
physical machine address.

Within one thread, `sequence` is unique. The execution model therefore derives
per-thread ordering without constructing or allocating an explicit edge list.

## 2. Sequenced-before

For events `a` and `b`:

```text
sequenced_before(a, b) :=
    a.thread == b.thread
    && a.sequence < b.sequence
```

Sequenced-before is irreflexive and defines the source/execution order visible
to the memory model within one thread.

## 3. Reads-from

An atomic read or read-modify-write may identify the atomic write/RMW event from
which it observed its value.

A valid reads-from witness requires:

- source and target are atomic;
- source writes;
- target reads;
- source and target name the same semantic location;
- the referenced source event exists.

Reads-from is explicit because value equality alone does not identify causal
provenance.

## 4. Synchronizes-with

Synchronizes-with is an explicit, validated inter-thread edge.

The foundational synchronization rule is direct release/acquire publication:

```text
release-like atomic write/RMW
        |
        | reads-from
        v
acquire-like atomic read/RMW
```

Release-like orders are:

```text
release
acq-rel
seq-cst
```

Acquire-like orders are:

```text
acquire
acq-rel
seq-cst
```

A direct synchronization edge is valid only when the target's reads-from
witness names the source event and both access the same location.

Relaxed operations therefore do not silently acquire or release merely because
they happen to observe the same value.

Chapter 67 adds explicit synchronization reasons for release sequences and
release/acquire fences without changing the definition of happens-before. The
reason and its witness event IDs remain visible in Semantic IR.

## 5. Happens-before

Oak defines happens-before as the transitive closure of:

```text
sequenced-before ∪ synchronizes-with
```

It is deliberately not reflexive.

The canonical publication chain is:

```text
thread 0                         thread 1

payload write
    |
    | sequenced-before
    v
release flag write
    |
    | synchronizes-with
    v
                              acquire flag read
                                   |
                                   | sequenced-before
                                   v
                              payload read
```

Therefore:

```text
payload write happens-before payload read
```

This theorem is formalized in Lean and execution-tested in the Semantic IR
model. It is the core fact required by an SPSC publication/consumption proof.
The richer synchronization rules in chapter 67 feed the same HB closure.

## 6. Conflicting accesses

Two memory events conflict when:

- they name the same location;
- neither is a fence;
- at least one writes.

Two reads alone do not conflict.

## 7. Data races

Two events constitute a data race when all of the following hold:

```text
different threads
&& conflicting accesses
&& at least one access is non-atomic
&& !happens_before(a, b)
&& !happens_before(b, a)
```

Oak deliberately treats mixed atomic/non-atomic conflicting access as subject
to the race rule. Making one side atomic does not bless an otherwise unordered
non-atomic access.

At the language level, ordinary `Atomic[T]` storage cannot currently be read or
written through ordinary value operations, which removes a large class of such
mixed accesses by construction. The execution definition remains fail-closed so
future unsafe/raw-memory facilities cannot weaken the semantic rule.

A data-race-free program may rely on the specified shared-memory semantics. The
language must not assign portable meaning to an execution containing a data
race merely because a particular backend appears to produce stable results.

## 8. Allocation and bounded-work contract

The executable Semantic IR model is intended for compiler verification,
property tests, deterministic simulation, and small-state execution checking.
It is not a hidden runtime service.

Its graph queries obey these structural rules:

1. event and synchronization arrays are supplied by the caller;
2. `happens-before` receives caller-owned `visited` and stack storage;
3. no map, queue, recursion, closure capture, or heap allocation occurs inside
   HB traversal;
4. race queries reuse the same workspace;
5. the maximum traversal stack is exactly the event count;
6. traversal work is finite and bounded by the supplied execution size;
7. zero internal allocations are regression-tested with `testing.AllocsPerRun`.

Chapter 67 preserves the same rule for release-sequence traversal: it walks
existing reads-from links with an event-count bound and no internal allocation.

The reference implementation currently favors simple auditable bounded scans
over sophisticated graph indexing. Faster representations may be added later as
refinements while preserving this semantic model.

## 9. Formal verification

`spec/lean/Oak/HappensBefore.lean` proves the abstract core relation laws:

- sequenced-before implies happens-before;
- synchronizes-with implies happens-before;
- happens-before is closed under transitivity;
- the release/acquire publication chain establishes HB from payload write to
  payload read;
- an established HB edge excludes the data-race predicate;
- therefore the canonical published payload pair is not a data race;
- the release-like and acquire-like order classifications contain the intended
  orders and exclude relaxed.

The same Lean module now also models release sequences and the fence
synchronization constructors from chapter 67, with publication theorems for
those paths.

These are mathematical language-level theorems. They do not yet constitute a
formal refinement proof from Go graph traversal to Lean or from generated C to
AArch64 instructions.

## 10. Executable verification

`semir/memory_model.go` and its tests exercise the same execution vocabulary:

- valid release/acquire publication;
- transitive HB across both thread-local and synchronization edges;
- an unsynchronized non-atomic conflict is a race;
- a mixed atomic/non-atomic unordered conflict is still a race;
- same-thread conflicting accesses are ordered and do not race;
- a relaxed reader cannot witness an acquire synchronization edge;
- a synchronization edge must agree with its reads-from source;
- undersized scratch fails explicitly;
- HB traversal performs zero internal allocations;
- race queries perform zero internal allocations;
- chapter-67 tests add modification-order, RMW-chain, release-sequence, and
  fence-mediated publication coverage.

The full repository Go/race suite and Lean build remain CI acceptance gates.

## 11. Status

| Layer | Status |
| --- | --- |
| event/reads-from vocabulary | specified + implemented |
| sequenced-before | specified + implemented |
| direct release/acquire synchronizes-with | specified + implemented + tested |
| happens-before definition | specified + implemented + Lean-modeled |
| publication theorem | proved in Lean + execution-tested |
| data-race definition | specified + implemented + Lean-modeled |
| zero-allocation HB/race traversal | regression-tested |
| modification order | specified + implemented in chapter 67 |
| release-sequence semantics | specified + implemented + Lean-modeled in chapter 67 |
| fence-mediated synchronization | specified + implemented + Lean-modeled in chapter 67 |
| Go-to-Lean refinement | not yet proved |
| seq-cst global order | next |
| compiler/C refinement | not yet proved |
| AArch64 weak-memory litmus suite | not yet implemented |

## 12. Next closure steps

Before higher-level lock-free structures depend on the memory model as a closed
contract, Oak should add:

1. sequential-consistency total-order constraints;
2. backend/compiler refinement tests;
3. AArch64 MP/SB/LB/IRIW-style litmus coverage and assembly inspection;
4. target lock-free admission rules for realtime profiles.

Only after those pieces are explicit should `SpscRing[T, N]` be treated as a
proof consumer of the complete machine-memory model rather than as an isolated
algorithm test.
