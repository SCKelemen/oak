# Optimizer artifact DAG

Status: OptIR analysis DAG with exact identities, checked selective reuse, and
bounded deterministic parallel execution; the complete native candidate path
from materialization through selection is also live. Typed artifact references
and arity-specific builders derive keys and decode dependencies for the OptIR
graph. This note refines the optimizer search design; it does not change Oak
semantics or authorize OptIR emission.

The experimental Wasm backend now uses the same typed graph infrastructure for
target/input → materialization → byte admission. Its returned graph report is
diagnostic: byte admission does not stand in for a native semantic verdict.
Both the OptIR root and the Wasm input boundary take owned CFG snapshots.
See [target emission pipelines](target-pipeline-2026-09.md) for the small shared
builder and the remaining target-specific boundaries.

## 1. Decision

Reusable, branching, independently verifiable, proof-gating, or expensive
compiler results should be represented as dependency graphs of immutable
artifacts. Straight-line frontend sequencing and local implementation-detail
cleanup remain ordinary deterministic code. `compiler.Stage.Then` is therefore
deliberately linear, while OptIR's reusable generic analysis chain and every
proposed native candidate's materialization and gates execute through artifact
graphs.

The boundary is demand-driven: a result deserves artifact identity when
another computation needs to cache it, reuse it, compare it, verify it, run it
concurrently, or bind evidence to its exact version. A private sequence such as
canonicalize → GVN → DCE may remain one `ScalarCleanup` node unless an
intermediate result gains one of those consumers. The compiler is a hybrid of
pipelines and artifact DAGs, not one global graph by decree.

The graph is about computation and evidence, not control-flow. An OptIR CFG may
contain cycles while the artifact graph that produced and analyzed that CFG is
acyclic.

```text
checked model
     |
structured OptIR
     |
    CFG v0 --------------------+
     |          |              |
    SCCP   loop structure    GVN/DCE
                |               |
                |             CFG v1
                |          /     |
                +-- preservation |
                         \        |
                     loop facts v1
                            |
                           LICM
                                |
                              CFG v2
                                |
                     structural admission
                                |
                         metrics and cost
                                |
                   semantic/assembly verdict
                                |
                             selection
```

Every edge states exactly which artifact a computation consumes. A transform
never updates a CFG node in place; it creates another version.

## 2. Required invariants

1. **Exact version ownership.** An analysis result belongs to one exact input
   artifact. It cannot be attached to another CFG merely because their function
   names or block shapes look alike.
2. **Immutable values.** Published artifact payloads are read-only. A transform
   clones its input and publishes a new artifact.
3. **Explicit prerequisites.** A node can run only after all dependencies have
   succeeded. Hidden reads of another pass's mutable state are forbidden.
4. **Verification is an artifact.** Admission and equivalence results are
   ordinary versioned dependencies, not booleans stored on mutable candidates.
5. **Selection is gated.** Cost can prioritize which candidate to validate, but
   final selection requires the verdict strength demanded by every transform.
6. **Identity remains available.** Candidate search retains the unmodified
   implementation and its required validation path as the fallback.
7. **Deterministic observation.** Registration order, worker completion order,
   and map iteration cannot change node identity, reports, the selected error,
   or the final selection tie-break.
8. **Failure is closed.** Missing dependencies, cycles, failed prerequisites,
   stale versions, cancelled work, and insufficient verdicts produce no
   selectable candidate.

## 3. Artifact identity

The first substrate uses:

```text
ArtifactKey {
    kind
    name
    version
}
```

`kind` distinguishes source, checked input, IR, analysis, candidate, admission,
metrics, cost, verdict, and selection artifacts. `name` describes the producer,
such as `optir.cfg`, `optir.loops`, or `native.aarch64.verify`. `version` names
the exact recipe and inputs.

Derived versions hash an implementation revision and the ordered dependency
keys with length-delimited fields. Changing a dependency version, dependency
order, kind, producer name, or implementation revision changes the result.
Root artifacts use a digest of their canonical input bytes or another stable
identity supplied by the owning frontend.

The key is a recipe identity, not permission to trust the payload. A buggy or
nondeterministic transform can still produce a wrong artifact under a stable
key; the independent verifier remains authoritative. Persistent caches must
also include the compiler build identity in the producer revision.

## 4. Node kinds and legal roles

| Kind | Examples | May authorize emission? |
| --- | --- | --- |
| source | module files, target description | no |
| checked | checked semantic model, proof facts | only as a stated source license |
| IR | structured OptIR, CFG, MachineIR | no |
| analysis | SCCP, dominance, loops, alias/range facts | no |
| candidate | GVN/DCE, LICM, vector or allocation plan | no |
| admission | CFG verifier, seam checker, cheap structural checks | only the boundary it explicitly checks |
| metrics | size, pressure, branch and memory estimates | no |
| cost | target-neutral or target-specific score | no |
| verdict | semantic equivalence, proof/license result | yes, at its declared strength |
| selection | cheapest sufficiently admitted candidate | chooses; proves nothing itself |

The generic graph executor schedules these kinds but does not infer semantic
permission from a kind name. `ArtifactRef[T]` and the typed root/unary/binary/
ternary builders derive exact ordered-dependency keys, extract inputs, and fail
closed on a missing or wrongly typed payload. They remove graph plumbing, not
proof obligations: stronger candidate/admission/verdict/selection edge rules
remain explicit compiler policy.

## 5. Costing and validation order

Costing an unverified candidate is safe because a score cannot make it
selectable. The efficient path is:

```text
proposal
  -> cheap structural admission
  -> metrics
  -> cost
  -> bounded validation queue in cost order
  -> expensive equivalence verdict
  -> final selection among sufficient verdicts
```

This avoids proving candidates already dominated on cost. A selection node must
depend on both the cost and sufficient verdict for every candidate it may
choose. A verifier refusal may create a refinement candidate, which is another
node with the refusal and original candidate as dependencies.

## 6. Analysis reuse and invalidation

The conservative rule is simple: a new IR version invalidates every analysis.
That is always correct. Selective reuse is permitted only when a transform
publishes a checked preservation certificate over named IR aspects:

```text
CFGTopology
SSAIdentity
OperationSemantics
MemoryEffects
Types
ProofFacts
Layout
```

Each current OptIR analysis has an immutable requirement declaration. A
certificate independently verifies both CFGs, binds their full content
fingerprints and exact artifact keys, then records domain-separated before and
after digests for every requested aspect. The redundant `preserved` field is
checked against digest equality and the whole certificate has an integrity
digest. It is analysis-reuse evidence only, never semantic equivalence or
permission to emit a candidate.

GVN/DCE is the first consumer. It preserves CFG topology but may change SSA
identity, operation semantics, types, and proof-fact placement. Loop analysis
is split accordingly: dominance and the natural-loop tree consume only
`CFGTopology`, so CFG v1 reuses the checked structure from v0. Affine
recurrences and trip counts are recomputed from v1's values and operations.
Unknown, trapping, call, and explicitly effectful operations all participate in
the conservative `MemoryEffects` digest; missing metadata never implies purity.

Reuse occurs only through the explicit certificate edge and only when it
covers every aspect in the consumer's declaration. There is no implicit
"probably unchanged" reuse.

## 7. Scheduling

The reference `Run` executor is deterministic and single-threaded. Each
executor:

- validates keys, dependencies, and acyclicity;
- computes only the transitive closure of requested targets;
- executes a shared dependency once;
- consults an exact-key cache before running a node;
- supplies dependency payloads in the node's declared order;
- records execution and cache evidence in stable topological order;
- observes cancellation between nodes;
- attributes an error to the exact failing artifact.

`RunParallel` uses deterministic ready waves. It removes at most the configured
worker count from the sorted ready set, runs those independent computations,
waits for the entire wave, and considers results in key order. A wave publishes
and caches all its results only when every task succeeds and the context remains
live. Otherwise every private result from that wave is discarded and the
earliest failing key wins, regardless of completion order. Earlier successful
waves remain useful cache entries, but a failed run publishes no target list.

Waves deliberately trade some pipeline utilization for reproducibility: worker
timing cannot change which later nodes start, the selected error, cache
contents, or trace. `ArtifactRun` still reports executed/cache-hit keys in the
canonical graph order. OptIR uses three workers, matching its current SCCP,
loop-structure, and GVN/DCE fan-out. Artifact computations must remain isolated
producers; the scheduler coordinates all cache reads and writes itself.

## 8. Cache rules

An artifact cache is keyed by the complete `ArtifactKey`. A cache hit is usable
only for that exact key. The scheduler never mutates a cached payload and never
stores a failed or cancelled computation.

The first in-memory cache is process-local. A persistent cache additionally
needs:

- compiler and optimizer implementation revisions;
- target description and ABI revision for target-dependent nodes;
- verifier/proof-kernel revision;
- stable canonical serialization of the artifact;
- corruption detection and bounded storage policy.

Eviction affects compile time only. A cache miss recomputes; it cannot alter
semantics or relax a gate.

## 9. Failure and cancellation

A graph with an empty key, duplicate task, duplicate edge, missing dependency,
or cycle is rejected before execution. A node failure prevents every dependent
node from running. Independent nodes outside the requested target closure never
run.

Cancellation in the sequential executor returns the context error attributed
to the next not-started node. The parallel executor stops after the current
wave, waits for its running computations, discards that wave, and retains no
partial selectable target graph.

## 10. Migration

Completed:

1. The generic graph, deterministic executor, derived versions, and
   process-local cache are in `opt/`.
2. The current OptIR analysis and transformation API is projected onto graph
   nodes. A changed final CFG can enter the separately gated native candidate
   path; artifact identity alone never licenses emission.
3. CFG v0 has a canonical fingerprint over every ordered semantic field. SCCP
   analyzes that exact key, and the exact-evidence SCCP rewrite publishes CFG
   v1. SCCP revision v2 adds closed constant-result scalar identities; its
   revision also flows into the composite memory-cleanup key, so old analysis
   or cleanup payloads cannot be reused under the new transfer rules. No new
   artifact node is needed. Loop analysis and GVN/DCE consume v1;
   GVN/DCE publishes CFG v2, a second
   loop node analyzes v2, and LICM consumes both v2 artifacts. LICM no
   longer recomputes loop analysis or dominance internally. Its loop facts are
   privately bound to their input fingerprint and integrity digest, so stale or
   mutated facts fail closed.
   After the checked memory transforms, one `optir.memory-cleanup` node
   composes SCCP, phi/GVN/DCE cleanup, fresh memory liveness and verified DSE,
   pure DCE, and a final pure LICM pass with fresh exact-CFG loop analysis.
   Its dependencies are the exact
   forwarding artifact and checked memory authority, and its revision includes
   the constituent analysis/rewrite revisions, including memory liveness and
   DSE, loop structure/analysis, and LICM. It rebuilds checked projection and
   MemorySSA after scalar/CFG rewrites and after final store/producer deletion
   and scalar motion. Native selection replays that
   bounded composition and uses the final CFG for bindings, call certificates,
   and materialization identity; intermediate helpers need no separate nodes.
4. OptIR has closed analysis-aspect declarations and checked preservation
   certificates. GVN/DCE's certificate is an admission artifact over exact CFG
   v1/v2 identities. The loop-structure artifact declares only `CFGTopology`,
   so v2 reuses v1 dominance/natural loops while recomputing induction facts.
5. Native search gives every proposal a canonical, pre-lowering recipe over
   its complete lane configuration, source/program inputs, and the checked fact
   domains nativegen reads. A checked input node feeds materialization, then
   typed candidate, admission, metrics, and cost nodes. Failed lowering
   publishes no candidate. The bounded validation loop requests one verdict
   target at a time in established cost order, so proof early-stop and budgets
   are unchanged. Final selection is an artifact whose possible choices each
   contribute explicit candidate, clean-admission, cost, and verdict edges. A
   weak verdict on a gated transform cannot produce a selection target without
   a separately validated ungated fallback. The per-search cache remains
   ephemeral while backend-owned `Config` and `Body` values lack canonical
   serialization and a deep freeze boundary.
6. The graph has bounded deterministic ready-wave concurrency. Reverse
   completion, worker bounds, deterministic failures,
   cancellation, exact-once dependencies, and cache pruning are race-tested.
7. Generic typed artifact references and arity-specific derived-task builders
   own dependency extraction and recipe-key derivation. Tests pin ordered
   identities and refusal of wrong cached payloads.

The compiler currently runs this graph without a cross-call cache. Public
OptIR results contain mutable slice-backed Go values, so sharing cached payloads
across API calls first requires a freeze-or-clone ownership boundary. The graph
and exact keys already support caching, and tests exercise both exact hits and
complete dependent invalidation after an input change.

Remaining:

8. Add persistent content-addressed caching only after canonical serialization
   and version invalidation are stable.

## 11. Non-goals of the first slice

- no emission license derived merely from an artifact edge;
- no persistent cache;
- no requirement that straight-line frontend stages or private local cleanup
  become artifact nodes;
- no analysis reuse across IR versions without a checked aspect certificate;
- no claim that a graph kind replaces a proof or verifier verdict;
- no requirement that language users understand or configure the graph.
