# Type system: v1 correctness and performance gates

Audit started 2026-10-08. Source baseline: `specification` at
`8735623eb6902b41d3516113bba9053e076031d0`. Initial implementation PR: #684.
This is an audit and proposed acceptance plan, not a claim that the complete
language, checker, self-hosted toolchain, or machine-code path has been proved.

## Release contract

For the admitted v1 language, acceptance by the production checker must imply
well-typed elaboration under the declarative typing, ownership, effect, and
representation rules. Well-typed execution must preserve those invariants and
not get stuck on a type/authority error, under explicit runtime, unsafe/FFI,
and platform assumptions. Divergence and specified traps are not silently
reclassified as type errors or proved absent. Both ARM64 and RV64 require the
representation and compilation refinements below; a frontend proof alone is
not a proof of either executable.

Performance is objective-relative: check time, proof time, peak memory,
incremental latency, and generated-code cost must be measured separately.
A synthetic speedup does not establish that the type system is optimal.

## First patch: constructor-complete inference traversal

At the baseline, `typechecker/hm.go` traverses records, functions, arrays,
and generic applications but omits unions, intersections, narrowed ADT type
arguments, buffer/atomic element types, and foreign-function signatures in
several variable walkers and in substitution. At the type-engine API boundary,
these omissions can hide occurs-check cycles, leave variables unsubstituted,
and lose monomorphic dependencies. Each constructor still needs a source-level
reachability assessment: a representable Go type object is not automatically
an admitted Oak source type.

The patch covers those constructors in substitution and shares a local,
iterative, identity-based graph walk across occurs checking, variable
collection, instantiation, and monomorphic lookup/marking. It preserves
constructor metadata and avoids persistent caches over mutable solutions.
Nominal declaration metadata, such as interface method scopes, is not treated
as a child of an inference type use.

A small-signature fast path uses local stack storage and a bounded identity
set, spilling to a map for larger graphs. Graph nodes are not revisited.
Anonymous record traversal is sorted; declared field order is retained.
This is not a general cycle-safe substitution implementation: the traversal's
visited set must not be mistaken for a proof that arbitrary cyclic substitution
maps are valid or that `Substitution.Apply` terminates on malformed inputs.

Committed regressions cover eleven constructor cases, 121 mixed-nesting
combinations, substitution composition and metadata preservation, fresh
instantiation, monomorphic dependency propagation, shared graph traversal,
record order, early stopping, small-set/stack spill, and nil walk inputs.
These are tests, not machine-checked soundness proofs.

## Validation and measurement boundary

An isolated Go 1.23.2 linux/amd64 harness ran the exact new
`type_variables.go` traversal with simplified surrounding type adapters.
The original traversal file was checked against its Git blob hash before the
small-signature revision. Traversal-only tests (including 121 nested pairs),
spill tests, and race runs passed locally. The harness deliberately does not
implement or validate production substitution, generalization, elaboration,
or backends. It is not a full-repository test and is not checked in as one.

Local traversal microbenchmarks used two 100 ms samples per case on an AMD
EPYC 9V74 host. The comparator reproduces the baseline collection algorithm
with the same adapters. Approximate ranges from that run:

| Shape | Baseline collection | Revised collection | Interpretation |
| --- | ---: | ---: | --- |
| One binder | 49-50 ns | 33-36 ns | Fast path helps. |
| Small function signature | 53-55 ns | 61-64 ns | Small remaining overhead. |
| Unshared depth-8 binary tree | 23-25 us | 68-69 us | About 3x slower; visited-set cost. |
| Shared depth-12 function DAG | 48-49 us | 0.48-0.52 us | Repeated graph expansion removed. |
| Shared depth-16 function DAG | 736-741 us | 1.53-1.66 us | Adversarial sharing improves substantially. |

Do not extrapolate these numbers to compiler throughput, proof throughput,
self-hosted execution, ARM64, or RV64. Non-shared tree regressions are explicitly
retained in the benchmark suite. Production profiles must decide whether the
representation, memoization, or walk implementation needs another revision.

Required integration commands, not claimed completed by the local harness:

```sh
go test -race ./typechecker
go test ./compiler -run '^TestE2EStdlibRing$' -count=1
go test ./typechecker -run '^$' -bench 'TypeVariable' -benchmem -count=5
```

The exact PR head must also pass applicable normal compiler, library, resource,
and formal checks before merge. Consult live CI, not this document, for status.

## Remaining work, in dependency order

### T1. Separate identity, unification, and value-flow compatibility

Audit `typechecker/typechecker.go`, `hm.go`, `lattice.go`, and
`lattice_identity.go` with minimal API and source regressions. Specific inspected
sites: `FunctionType.Equals` and `unifyFunction` do not compare `Variadic`;
`RecordType.Equals` handles empty records before its nominal-struct check;
`Unify` uses the broader `Equals` compatibility relation as an early success.
Do not label every site a source-level exploit without demonstrating reachability.

Define and test distinct relations for strict type identity, inference
unification, semantic inclusion, value assignability, record-shape satisfaction,
and representational equivalence. Representation equality never grants nominal
identity, write authority, stronger alignment, or an unproved refinement.
Cover open/closed records, narrowed variant/parent direction, module-qualified
names, phantom states, spans/views, and variadic signatures. Preserve explicitly
intended compatibility rules while removing inappropriate inference shortcuts.

### T2. Binder-scoped generalization and instantiation

Audit `findFreeTypeVars`, `extractBoundTypeVars`, and
`quantifiedSubstitution`. The baseline still stores quantified names in schemes
and finds environment exclusions by names even though substitutions use binder
pointers. Establish the intended free-variable-of-environment rule by binder
identity; do not accidentally re-generalize an environment variable or conflate
distinct same-spelling binders. Preserve quantified versus free variable scopes.

Retain effect/authority value restrictions through aliases, closures, matches,
and higher-order calls. Failed checking attempts must roll back all tentative
specializations. Successful equations must compose consistently and keep
escaped monomorphic dependencies closed. Constraints must be discharged at
every supported instantiation boundary, not merely transported as metadata.

### T3. Complete source-level typing and authority matrix

Add acceptance/rejection cases spanning ADT constructors, GADT branch-local
refinements, exhaustiveness, records, generic constraints, integer widths and
literals, refinement construction/erasure, array lengths, ownership modes,
mutable storage, aliasing, effects, unsafe/FFI, and host capabilities.

Prohibit authority creation through subtyping or container conversions.
Invalidate extent/alignment facts after relevant writes and calls. Type safety
must include storage lifetime and initialization, not just expression tags.
Semantic inclusion in `any` or a union is not permission to silently box,
allocate, invent a tag, or change the calling convention.

### T4. Prove the core and refine the actual checker

Define the admitted core, elaboration, environments, substitutions, heap/store
invariants, and allowed effects. Prove substitution and scope preservation,
algorithmic acceptance soundness, preservation, and progress modulo specified
outcomes. Scope any completeness claim to a stated decidable fragment.

Connect the production checker implementation to those judgments, including
parsing of annotations, constraint discharge, error propagation, and caches.
Existing lattice-subsystem proofs must not be presented as a full language
soundness proof. Tests, model proofs, and implementation refinements need
separate evidence entries and explicit assumptions.

### T5. Optimize the measured bottlenecks for self-hosting

Profile bootstrap and eventual Oak checkers on the compiler, prover, and stable
stdlib corpus. Compare cold/warm checking, allocations, memory, and pathological
inputs; retain negative cases so a faster checker cannot merely skip checks.

Candidate architecture: immutable interned type constructors with compact
TypeIds; separately mutable inference variables with level/occurs invariants
and rollback; shared DAG substitution with identity-aware memoization; compact
work queues and visitation storage. Interning must include nominal identity,
parameters, phantom/state markers, authority, and representation-relevant facts.
Never intern distinct unsolved variables merely because their labels match.

The existing lattice normalizer distributes intersections over unions into DNF.
Measure clause growth; use checked fast paths and bounded symbolic algorithms
before eager expansion becomes an adversarial compile-time problem. A budget
exhaustion is a diagnostic/unknown result, never a successful subtype judgment.

Cache keys must include every semantic dependency: source/import revisions,
resolved binders, solver/substitution epoch or immutability boundary, live facts,
feature profile, and target layout where relevant. Check invalidation and
rollback against an uncached reference. Do not introduce memoization across
mutable inference states without that argument.

### T6. Self-hosted agreement and ARM64/RV64 refinement

Implement the same checking contract in Oak, with independent declarative
reference checks and differential tests against the bootstrap implementation.
Agreement alone does not establish correctness if both share the same bug.
Measure and prove the memory/arena algorithms used by the Oak checker itself.

Carry typed/authority evidence into SemIR and through specialization,
optimization, representation lowering, and runtime interfaces. For each target,
prove preservation of integer semantics, layouts, tags, alignment, calling
conventions, ownership-relevant memory behavior, and emitted operations.
Connect this to assembler encoding, linker relocations, startup, and final bytes.
ARM64 and RV64 are both release gates, not interchangeable evidence.

## Completion record

For each v1 feature retain: normative rule; accepting and rejecting examples;
Go implementation; Oak implementation; proof theorem and assumptions; SemIR
obligation; ARM64 obligation; RV64 obligation; regression suite; benchmark;
and exact-commit CI evidence. No feature is labelled fully proved while one of
its required links is only a test, a TODO, or an unchecked assumption.
