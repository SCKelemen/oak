# Bounded remap/reclamation protocol pilot

This is a **hand-written protocol abstraction**, not an execution of Oak,
Arm ASL/Sail, or the ARM weak-memory model. Passing it is bounded
model-checking evidence; it grants no optimizer permission and discharges no
Lean refinement premise. Stateright is pinned to 0.31.0, Rust to 1.91.1, and
all resolved registry dependencies/checksums are committed in `Cargo.lock`.

## Model and assumptions

There are two abstract observers and one serialized updater, one address
space, one mapping, two distinct pages (`Old` and `New`), and exactly one
remap. All four initial empty/old-cache combinations are checked. Each
observer has a separately propagated descriptor, optional cached translation,
one optional in-flight sampled translation/access, and service/acknowledgement
bits. There are no generation counters that grow without bound.

The updater issues a break, requests invalidation, waits for completion,
makes the new mapping, and reclaims the old page. Separate observer actions
propagate descriptors, service invalidation, acknowledge, and perform accesses.
The safe policy requires:

- Every observer has seen the break before invalidation is issued.
- An observer drains its in-flight access before servicing invalidation.
- Service clears that observer's cached translation before acknowledgement.
- All observers acknowledge before the updater declares completion.

These are **assumed operational contracts**, not implementations of DSB,
TLBI, ISB, shareability, broadcast, or hardware table walks. Publication is a
deliberately explicit per-observer transition; there is no implicit global
flush. An in-flight access samples a page and can later access it and refill
the cache, exposing the danger of acknowledging too early. This is not a
claim that actual ARM walks behave exactly this way, or that this model
overapproximates every ARM execution. Invalid descriptors simply disable new
accesses; architectural fault paths are omitted.

## Obligations and negative controls

Three safety properties require acknowledgements before reclamation, absence
of old references after reclamation, and no access to the reclaimed page.
Three reachability properties require an old-page access, an in-flight old
access, and a completed remap with a new-page access. Reachability is a
nonvacuity check, not a fairness or liveness theorem.

Four policy mutants separately skip the publication wait, in-flight drain,
invalidation service, or completion wait. Each must produce a replayable
old-reference and actual stale-access counterexample. The completion-wait
mutant must additionally violate the acknowledgement property. `Reclaim`
does not directly test the safety predicates: the preceding protocol must
establish them. Unit tests protect that distinction.

## Complete exploration of the declared finite model

The runner uses single-thread BFS without symmetry, depth/state/time cutoffs,
or property-driven early termination. The state type has a conservative
559,872-state bound per policy; this is not a search limit.

Stateright 0.31.0 uses fingerprints. A second traversal stores full states in
an equality-checking `HashSet` and runs to an empty work queue. The harness
compares its **entire reachable state set**, transition count, and every
safety/reachability outcome with Stateright's evaluated states. Coverage loss
from fingerprint merging therefore cannot silently pass this cross-check.
Both traversals share the transition relation: they do not independently
validate the abstraction or the Rust compiler/runtime.

An always-true `enumeration_sentinel` prevents the pinned BFS's internal
all-properties-discovered early exit, including in broken policies. It is
bookkeeping and is not counted as a substantive safety property.
`finish_when(AnyOf(empty))` also disables the outer discovery-based stop.
Every reported discovery is replayed from an allowed initial state, checking
each listed action, resulting state, and final predicate. Counterexamples are
not claimed to be shortest. Dropped, reordered, forged, and partial traces,
and missing/duplicate/extra visited states, have rejection tests.

Only after all five runs validate does the CLI emit JSON to stdout. An
interruption, timeout, panic, coverage discrepancy, unexpectedly safe mutant,
or unreachable positive example is a failure, not a successful partial run.
The CI job has a wall-clock timeout but no mechanism to reinterpret it as
successful exploration. The explorer web server and actor runtime are unused.

## Run

From this directory, with the pinned toolchain installed:

```sh
cargo fetch --locked
cargo fmt --all --check
cargo clippy --locked --offline --all-targets -- -D warnings
cargo test --locked --offline
cargo run --locked --offline --release > report.json
```

The report contains bounds, completion/coverage results, counts, property
outcomes, and replayed witnesses for each policy. CI uploads it alongside the
lockfile. The tool accepts no command-line options that could silently weaken
the configured search.

The [2026-09-28 local results](results/2026-09-28.md) record completed searches,
negative controls, validation, and the remaining architectural gaps.

## Relation to the existing proof chain

`spec/sail/lean/MemoryEventProjection.lean` preserves occurrences in a supplied
request view. This pilot does not supply that missing original-model trace
provenance. Nor does it classify events as CAT W/TTD or prove coherence,
translation, invalidation scope, context synchronization, or publication.

The official-model tests in `semir/aarch64_herd_test.go` remain a separate
oracle, including the pinned synchronized/unsynchronized AArch64-BBM catalogue
cases. They are not generated from these Rust counterexamples. The next
architectural step is an explicit, audited relation from protocol actions to
actual execution events and checks under the pinned CAT model. A sequential
interleaving result must never substitute for that relation.

Other omitted dimensions include multiple remaps/VMIDs/mappings, identifier
reuse/ABA, message failures/duplication, multiple outstanding accesses, faults,
interrupts, concurrent updaters, fairness, allocation ownership, and actual
Oak-to-assembly correspondence. No timings or Apple-Silicon performance
claims follow from this pilot.

Primary references: [Stateright Model](https://docs.rs/stateright/0.31.0/stateright/trait.Model.html),
[Checker](https://docs.rs/stateright/0.31.0/stateright/trait.Checker.html),
[project](https://github.com/stateright/stateright).
