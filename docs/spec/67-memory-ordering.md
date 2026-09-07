# Memory ordering: modification order, release sequences, and fences

This chapter extends the core execution model in `66-memory-model.md` with the
ordering witnesses needed by lock-free algorithms: per-location atomic
modification order, release sequences, and explicit fence-mediated
synchronization.

The governing rule is:

> If synchronization matters to correctness, the execution witness must say
> exactly which write, read, RMW chain, or fence established it.

Oak does not infer synchronization from equal values, wall-clock order, source
proximity, or a backend instruction that merely looks strong enough.

## 1. Per-location modification order

Every represented atomic write or read-modify-write carries:

```text
has_modification = true
modification : u32
```

The index belongs to the semantic atomic location. Two represented writes to
the same location may not have the same modification index.

For write-like atomic events `a` and `b`:

```text
modification_before(a, b) :=
    a.location == b.location
    && a.has_modification
    && b.has_modification
    && a.modification < b.modification
```

Modification order is separate from:

- per-thread sequenced-before;
- reads-from;
- synchronizes-with;
- happens-before.

They answer different questions and are never conflated in Semantic IR.

### 1.1 RMW adjacency

An RMW replaces the value it observes. For represented modification `n > 0`,
Oak therefore requires the RMW's reads-from witness to identify modification
`n - 1` on the same location.

An RMW at modification zero may observe the implicit initialized value and has
no represented reads-from source.

This rule gives Oak an explicit causal witness for the RMW chain rather than
reconstructing one later from integer indices alone.

## 2. Release sequences

A release sequence has:

1. a release-like atomic write/RMW head;
2. zero or more following RMW members;
3. every following member reads-from the immediately preceding modification.

Release-like means:

```text
release
acq-rel
seq-cst
```

An ordinary atomic store by any thread terminates the sequence. Relaxed RMWs do
not: their RMW/read-from relation preserves the causal chain back to the release
head.

For example:

```text
M0: release store
      |
      | next RMW / reads-from
      v
M1: relaxed RMW
      |
      v
M2: relaxed RMW
```

`M0`, `M1`, and `M2` are all members of the release sequence headed by `M0`.

If an acquire-like atomic read observes `M2`, the synchronizes-with edge is from
**M0**, not merely from M2. Thus payload state sequenced before M0 is published
to code sequenced after the acquire.

This rule is directly useful for CAS loops and future MPSC structures.

## 3. Fence events

A fence is an atomic ordering event with no memory location, reads-from edge, or
modification-order index.

Release-like fences are:

```text
release fence
acq-rel fence
seq-cst fence
```

Acquire-like fences are:

```text
acquire fence
acq-rel fence
seq-cst fence
```

Fences do not synchronize merely by existing. A fence synchronization edge
requires ordinary atomic read/write witnesses around it.

## 4. Explicit synchronization kinds

Semantic IR retains the reason for every synchronization edge.

### 4.1 Direct release/acquire

```text
release-like atomic write W
             |
             | reads-from
             v
acquire-like atomic read R
```

The edge is `W -> R`.

### 4.2 Release-sequence/acquire

```text
release head H -> RMW ... -> member M
                              |
                              | reads-from
                              v
                        acquire read R
```

The edge is `H -> R`.

### 4.3 Release fence -> acquire read

```text
release fence F
      |
      | sequenced-before
      v
atomic write W
      |
      | reads-from
      v
acquire read R
```

The edge is `F -> R`.

The write may itself be relaxed. The fence supplies the release semantics; the
write/read pair supplies the inter-thread value witness.

### 4.4 Release write/sequence -> acquire fence

```text
release head H -> optional RMW sequence -> member M
                                            |
                                            | reads-from
                                            v
                                      atomic read R
                                            |
                                            | sequenced-before
                                            v
                                      acquire fence F
```

The edge is `H -> F`.

The intervening read may be relaxed. The acquire fence supplies the acquire
semantics.

### 4.5 Release fence -> acquire fence

```text
release fence F0
      |
      | sequenced-before
      v
atomic write W
      |
      | reads-from
      v
atomic read R
      |
      | sequenced-before
      v
acquire fence F1
```

The edge is `F0 -> F1`.

Both witness event IDs are retained in Semantic IR so a debugger or proof
projection can explain exactly why the fences synchronize.

## 5. Happens-before remains simple

None of these rules changes the definition from chapter 66:

```text
happens-before = transitive closure(
    sequenced-before union synchronizes-with
)
```

The richer ordering layer only determines which synchronizes-with edges are
valid.

That separation is intentional. Higher-level proofs can reason about HB without
reimplementing every hardware-facing synchronization rule.

## 6. Fail-closed witness validation

The execution validator rejects, among other malformed executions:

- an atomic write/RMW with no modification index;
- a read/fence/non-atomic event carrying a modification index;
- duplicate modification indices on one location;
- an RMW whose represented predecessor is not modification `n - 1`;
- a release sequence that crosses an ordinary store;
- a release-sequence edge whose acquire does not read a sequence member;
- a release fence whose write witness is not sequenced after it;
- an acquire fence whose read witness is not sequenced before it;
- a fence-fence edge whose read did not read from the named write;
- witness IDs that are absent, out of range, or semantically the wrong kind.

A malformed witness never degrades to a stronger implicit synchronization rule.

## 7. Allocation and performance contract

The ordering model remains verification/tooling infrastructure rather than a
runtime scheduler service.

Structural requirements:

1. event arrays and synchronization edges are caller-owned;
2. modification order is an inline integer field on write-like events;
3. release-sequence membership walks existing reads-from links;
4. the maximum release-sequence walk is bounded by event count;
5. no hash map, linked node, recursive stack, or heap-backed worklist is needed;
6. release-sequence membership performs zero internal allocations;
7. HB/race traversal retains its caller-owned scratch contract from chapter 66.

The current representation intentionally chooses straightforward bounded scans
and links over premature graph indexing. A later optimized representation must
be a refinement of these semantics and demonstrate a real workload benefit.

## 8. Formal verification

`spec/lean/Oak/HappensBefore.lean` now includes:

- an inductive release-sequence relation headed by a release operation and
  extended one RMW step at a time;
- a synchronization relation with distinct proof constructors for direct
  release/acquire, release-sequence/acquire, release-fence/acquire,
  release/acquire-fence, and release-fence/acquire-fence;
- a theorem that reading any release-sequence member with an acquire operation
  carries the head's publication to later payload reads;
- a theorem for release-fence publication;
- a theorem for fence-to-fence publication;
- the existing fact that any established HB edge excludes the data-race
  predicate.

The Lean relation is mathematical language semantics. A direct refinement proof
between the Go validator/walk and the Lean definitions remains future work.

## 9. Executable tests

The Semantic IR test suite includes:

- a multi-thread release head followed by relaxed RMWs and an acquire consumer;
- exact per-location modification-order checks;
- a non-RMW store breaking the release sequence;
- rejection of an RMW that skips its immediate predecessor;
- rejection of duplicate modification indices;
- release-fence -> acquire-read publication;
- release-write -> acquire-fence publication;
- release-fence -> acquire-fence publication;
- rejection when fence witnesses appear on the wrong side of a fence;
- zero-allocation release-sequence membership regression;
- all chapter-66 HB/race tests under the stronger event validation rules.

## 10. Verification status

| Layer | Status |
| --- | --- |
| per-location modification-order vocabulary | specified + implemented |
| RMW predecessor rule | specified + implemented + tested |
| release-sequence relation | specified + implemented + Lean-modeled |
| release-sequence publication | Lean-proved + execution-tested |
| release-fence -> acquire | specified + implemented + tested |
| release -> acquire-fence | specified + implemented + tested |
| release-fence -> acquire-fence | specified + implemented + Lean-modeled + tested |
| zero-allocation release-sequence walk | regression-tested |
| implementation-to-Lean refinement | not yet proved |
| sequential-consistency total order | specified + implemented + Lean-modeled in chapter 68 |
| C/backend weak-memory refinement | next major layer |
| AArch64 litmus/assembly validation | next major layer |

## 11. Next closure layer: backend refinement

Chapter 68 defines the explicit global seq-cst witness and ties it to HB,
modification order, and read visibility. The language-level relation set is
therefore explicit enough to stop inventing semantics in the backend.

The next work is to verify that generated C and AArch64 code preserve these
relations through assembly inspection and weak-memory litmus tests. Only then
should a lock-free queue be accepted as relying on Oak's memory model end to
end.
