# Optimizer artifact DAG

Status: generic executor plus the first OptIR analysis migration. This note
refines the optimizer search design; it does not change Oak semantics or
authorize OptIR emission.

## 1. Decision

Oak's compiler stages, optimizer analyses, transforms, validation, costing, and
selection should be represented as one dependency graph of immutable
artifacts. `compiler.Stage.Then` remains linear and native candidate search
still owns an internal branching search. OptIR's first generic analysis chain,
however, now executes through the artifact graph rather than direct calls.

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
    SCCP     loop facts      CSE/DCE
                                |
                              CFG v1
                                |
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
| candidate | CSE/DCE, LICM, vector or allocation plan | no |
| admission | CFG verifier, seam checker, cheap structural checks | only the boundary it explicitly checks |
| metrics | size, pressure, branch and memory estimates | no |
| cost | target-neutral or target-specific score | no |
| verdict | semantic equivalence, proof/license result | yes, at its declared strength |
| selection | cheapest sufficiently admitted candidate | chooses; proves nothing itself |

The generic graph executor schedules these kinds but does not infer semantic
permission from a kind name. Typed compiler builders will impose the stronger
candidate/admission/verdict/selection edge rules.

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
That is always correct and is the first migration target.

Later, a transform may publish a checked preservation certificate over named IR
aspects:

```text
CFGTopology
SSAIdentity
OperationSemantics
MemoryEffects
Types
ProofFacts
Layout
```

For example, CSE/DCE preserves CFG topology but changes SSA identity and
operation semantics; dominance and the natural-loop block tree can be reused,
while recurrence and value-use analyses cannot. Reuse occurs only through an
explicit preservation edge checked against the analysis's declared aspect
dependencies. There is no implicit "probably unchanged" reuse.

## 7. Scheduling

The first executor is deliberately deterministic and single-threaded. It:

- validates keys, dependencies, and acyclicity;
- computes only the transitive closure of requested targets;
- executes a shared dependency once;
- consults an exact-key cache before running a node;
- supplies dependency payloads in the node's declared order;
- records execution and cache evidence in stable topological order;
- observes cancellation between nodes;
- attributes an error to the exact failing artifact.

This establishes graph semantics before introducing concurrency. The compatible
parallel scheduler maintains a sorted ready set, runs at most a configured
number of independent nodes, publishes results only after a node completes, and
chooses errors by deterministic graph order rather than completion time.
Per-function analyses are natural parallel work; within one function, SCCP,
loop analysis, and other readers of one immutable CFG can also run concurrently.

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

Cancellation returns the context error attributed to the next not-started node.
The future parallel executor will stop admitting new work, wait for already
running computations to publish or discard their private results, and retain no
partial selectable graph.

## 10. Migration

Completed:

1. The generic graph, deterministic executor, derived versions, and
   process-local cache are in `opt/`.
2. The current OptIR analysis API is projected onto graph nodes without
   changing its analysis results or emission behavior.
3. CFG v0 has a canonical fingerprint over every ordered semantic field. SCCP,
   loop analysis, and CSE/DCE consume that exact key. CSE/DCE publishes CFG v1,
   a second loop node analyzes v1, and LICM consumes both v1 artifacts. LICM no
   longer recomputes loop analysis or dominance internally. Its loop facts are
   privately bound to their input fingerprint and integrity digest, so stale or
   mutated facts fail closed.

The compiler currently runs this graph without a cross-call cache. Public
OptIR results contain mutable slice-backed Go values, so sharing cached payloads
across API calls first requires a freeze-or-clone ownership boundary. The graph
and exact keys already support caching, and tests exercise both exact hits and
complete dependent invalidation after an input change.

Remaining:

4. Add analysis-aspect declarations and checked preservation certificates.
5. Move native candidate materialization, seam checking, semantic validation,
   cost, and selection onto typed graph builders while retaining identity.
6. Add bounded ready-node concurrency and deterministic tracing.
7. Add persistent content-addressed caching only after canonical serialization
   and version invalidation are stable.

## 11. Non-goals of the first slice

- no code-emission change;
- no persistent cache;
- no speculative analysis reuse across IR versions;
- no parallel executor yet;
- no claim that a graph kind replaces a proof or verifier verdict;
- no requirement that language users understand or configure the graph.
