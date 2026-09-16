# Memory model: executions, happens-before, and data races

This chapter defines the execution-graph core beneath Oak concurrency. It is the
semantic bridge between source-level atomic operations and higher-level queues,
channels, schedulers, device protocols, and realtime code.

The governing rule is:

> Shared-memory correctness is an explicit relation between events, not an
> accidental consequence of compiler or processor behavior.

This chapter intentionally separates the layers:

1. **What is happens-before and what constitutes a data race?** This chapter
   specifies and implements those core relations.
2. **Which synchronization witnesses are valid?** `67-memory-ordering.md`
   extends the same execution model with modification order, release sequences,
   and fence-mediated synchronization.
3. **How are all seq-cst events globally ordered?** `68-sequential-consistency.md`
   defines the separate SC witness and its HB, modification-order, and read
   visibility constraints.

The AArch64 ordered-before projection and its MP/SB/IRIW theorems are in Lean.
The matching litmus programs execute in CI against Arm's official CAT model at
pinned Herdtools7 commit `76d5bd259d4c4b553a0f52158b9638559b79a5b5`.
That gate byte-checks the pinned CAT source and certifies the restricted full-
and load-DMB `bob`, full-DSB `DSB-ob`, structural `IFB-ob`, and `obs` inclusion
chains from Herd's include-expanded parser AST. Lean now mirrors the pinned
`TTDINV | TTDAF0` and `(TTD & M) \ TLBUncacheableTTD` membership formulas and
projects already classified descriptor actions through an explicit one-way
soundness premise. It also spells the complete seven-operand `BBM` relation
over supplied occurrence predicates and proves the local maintenance witness
inhabits it under separate one-way `ca`, TLBI-membership, and `inv-scope`
obligations. Its two local DSB edges now reach `ob` through an exact projection
of the unconditional full-DSB arm, including `M | DC.CVAU | IC | TLBI` source
membership and the complete implicit-event destination exclusion. CAT `po`,
set membership, arm inclusion, and `ob` transitivity remain supplied facts.
Lean's kernel checks fully expanded `Iff.rfl` formulas for that source,
destination, and shared-event arm; the adjacent lexical source-drift guard
pins the projected definitions' spelling but does not decide command
elaboration.
Construction of those primitive predicates, a complete formal
semantics of CAT, and the occurrence-indexed instruction-to-event bridge remain
open. The adjacent Sail proof conditionally projects aligned ordinary STR64
data through the pre-`__WriteMemory` pair to the no-device model's selected
external `write_ram` arguments `(56, 8, defaultRAM, PA, data)`. The default-RAM
register value remains an explicit input, and the projection proves neither
route/call reachability nor memory mutation or event generation.

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

Chapter 67 preserves the same rule for release-sequence traversal, and chapter
68 keeps the global SC witness caller-owned while reusing the HB workspace.

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

The same Lean module also models release sequences and the fence synchronization
constructors from chapter 67. `Oak.SequentialConsistency` models the global SC
order, its HB/MO consistency, and SC-read visibility from chapter 68.

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
- chapter-67 tests cover modification order, RMW chains, release sequences, and
  fence-mediated publication;
- chapter-68 tests cover global SC membership/order and SC-read visibility.

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
| seq-cst global order and read visibility | specified + implemented + Lean-modeled in chapter 68 |
| Go-to-Lean refinement | not yet proved |
| compiler/C refinement | instruction families checked; decoded DMB/DSB records index the restricted Lean ordering relations; descriptor action-to-projected-CAT-tag soundness is an explicit premise; C/LLVM, trace/tag extraction, DSB completion, ISB context synchronization, and complete CAT semantics remain open |
| AArch64 weak-memory litmus suite | eleven scalar language/machine cases + two byte-pinned official BBM/VMSA catalogue cases + inductive Lean `ob` projection for full/load DMB and full DSB + pinned descriptor classifier formulas + official-CAT AST certificate and Herd execution gated |

## 12. Next closure steps

The language-level relation set is now explicit. Before higher-level lock-free
structures depend on it end to end, Oak should verify refinement through:

1. keep the generated-C memory-order/assembly tests tied to the selected
   instruction classes;
2. extend the mechanically pinned `Oak.AArch64WeakMemory` subset into a formal
   CAT semantics and discharge the current one-way descriptor-tag premise by
   connecting emitted instructions to Arm event tags, `rf`, and `ca`;
3. target lock-free admission — in place for the C backend as a per-carrier
   static assertion (65-machine-memory.md §6); a realtime profile may still
   want it to refuse `OAK_ATOMIC_ACCEPT_LOCKED`;
4. direct implementation-to-Lean refinement for the most load-bearing pieces
   where the proof cost is justified.

Only after the compiler/machine projection is demonstrated should
`SpscRing[T, N]` be treated as a proof consumer of Oak's memory model rather
than as an isolated algorithm test.
