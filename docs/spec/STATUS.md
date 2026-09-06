# Oak Feature and Verification Status

This matrix is intentionally conservative. A historical document saying “complete” is not sufficient evidence for current implementation/proof status.

Legend:

- **S** specified normatively in `docs/spec/`
- **I** implementation exists and is intended to implement the normative feature
- **T** implementation tests exercise the normative laws
- **M** machine-checkable formal model exists
- **P** stated formal properties are mechanically proved/model-checked
- **R** implementation-to-model refinement/correspondence is machine-checked

| Feature | S | I | T | M | P | R | Notes |
| --- | :---: | :---: | :---: | :---: | :---: | :---: | --- |
| Layout + explicit blocks | ✓ | ✓ | ✓ | ✓ | ✓ |  | Go tests cover explicit/layout token-kind equivalence, original significant-token preservation, balanced virtual braces, continuation contexts, dedent ordering, and zero-width synthetic spans; `Oak.Layout` proves abstract source-order preservation, virtual-stack balance, EOF closure, and close-underflow rejection; indentation-trigger refinement pending |
| Source spans / UTF-16 editor positions | ✓ | ✓ | ✓ | ✓ | ✓ |  | `Oak.SourcePosition` proves UTF-8/UTF-16 scalar-width rules, additive coordinate accumulation, monotonic offsets, and ASCII width equivalence; Go tests cover emoji, multiline positions, byte-boundary rejection, links, and LSP coordinates; refinement pending |
| First-class diagnostics | ✓ | partial | ✓ | ✓ | ✓ |  | `diagnostic.Diagnostic` has stable code/category, one primary label, secondary labels, structured notes/help, deterministic plain rendering, and validation; `Compilation.Check` preserves structured type diagnostics instead of flattening them. Generic constraint/record-shape failures, match coverage/redundancy/unreachable-state failures, and the first borrow/view/span conflict family use specific stable codes and causal context. `source.Location` establishes canonical source identity; `Oak.Diagnostics` proves retitling/advice/secondary context preserve stable identity and primary cause. Parser/general type/effect/representation diagnostics, canonical byte-location threading into every diagnostic, code-frame rendering, broader cascade suppression, and implementation refinement remain pending |
| Delimited parser cursor contract | ✓ | ✓ | ✓ | ✓ | ✓ |  | one `parseDelimited[T]` path covers invocations, parameters, type arguments, and array elements; `Oak.Delimited` proves canonical opener/body/close structure, item preservation, unique close suffix, exact close offset, and trailing-separator semantic transparency; refinement pending |
| Type lattice (`never`, `any`, join/meet) | ✓ | ✓ | ✓ | ✓ | ✓ |  | Go subtype decision procedure is aligned with the proved distributive-lattice laws; explicit implementation refinement is still pending |
| Type inference | ✓ | partial | partial | partial | partial | partial | Oak uses unification/type-scheme machinery where useful but inference is layered with constraints, refinements, ownership/effects/regions, representation and proof obligations. Binder identity is distinct from source-facing names; `Oak.TypeVarIdentity` proves substitution isolation for same-named distinct binders. `Oak.GenericConstraintRefinement` proves scoped direct/unary constrained inference plus accumulated multi-parameter, repeated-binder and binary generic-application paths. Principal/general inference, richer refinements and exported-signature checking remain pending |
| Polymorphic generalization safety | ✓ | partial | ✓ | ✓ | ✓ |  | `GeneralizeWithFacts` keeps inferred monotypes unchanged while blocking universal quantification when mutable, unique, region, external, effectful, unsafe, or unresolved authority is present. `Oak.GeneralizationSafety` proves safe facts permit generalization and each modeled authority barrier blocks it. Producing these facts automatically from ownership/effect/region analysis and implementation refinement remain pending |
| Semantic records/products | ✓ | ✓ | ✓ |  |  |  | plain `{ ... }` is parsed as a semantic product and projects semantic fields while leaving representation unspecified; source order is preserved as declaration metadata; duplicate fields are rejected |
| Record shape constraints | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | `Oak.RecordShapeRefinement` proves the concrete name-lookup/exact-type decision procedure equivalent to `Oak.RecordShape.Satisfies`. `Oak.GenericConstraintRefinement` additionally proves the implemented direct `T: Shape` call path and one unary-container inference path succeed exactly when the abstract shape obligation holds and return exactly the substituted semantic result. **R is scoped to these modeled record-shape paths**, not arbitrary inference programs or method-interface constraints. |
| Representation polymorphism | ✓ | ✓ | ✓ | ✓ | ✓ |  | `RepresentationRegistry` permits multiple named representation bindings for one semantic definition; selection rebinds only `Definition.Representation`; ordinary resolved record representations must cover semantic fields exactly once. `Oak.RepresentationPolymorphism` proves semantic identity and shape satisfaction are representation-independent; registry implementation refinement pending |
| Natural struct representation selection | ✓ | ✓ | ✓ |  |  |  | parser preserves `struct { ... }` distinctly from `{ ... }`; `type = struct { ... }` selects `RepresentationRecord + natural-ordered` while remaining unresolved until target field representations are known |
| Natural struct layout | ✓ | ✓ | ✓ | ✓ | ✓ |  | `NaturalRecordLayout` computes checked ordered non-packed layout with power-of-two alignment and uint32 overflow rejection; `Oak.RecordLayout` proves identity/order preservation, field alignment, non-overlap, and final-size alignment in the unbounded arithmetic model; implementation refinement pending |
| Record composition | ✓ | partial | partial |  |  |  | semantic composition is separated from subtyping and from representation composition |
| ADTs | ✓ | ✓ | ✓ |  |  |  | old payload/default/tag meanings need compiler reconciliation |
| Pattern matching | ✓ | ✓ | ✓ | partial | partial |  | canonical `=>`; constructor/payload narrowing exists; recursive coverage analysis is formalized separately; legacy surface aliases remain implementation concern |
| Exhaustiveness | ✓ | ✓ | ✓ | ✓ | ✓ |  | recursive coverage tree distinguishes constructor payload cases, finite `Bool`, and open scalar domains; counterexamples are deterministic source-level pattern witnesses; malformed patterns suppress derivative coverage errors. `Oak.Exhaustiveness` proves finite constructor coverage laws and `Oak.PatternAnalysis` proves reachable-case coverage/counterexample laws; implementation refinement pending |
| Pattern redundancy / reachable-state analysis | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | source-order usefulness detects subsumed arms; existing narrowed constructor facts restrict the reachable case universe; impossible/redundant arm bodies are treated as `never` and do not widen match results. `OAK-T0202`/`OAK-T0203` are structured unnecessary-code warnings. `Oak.PatternAnalysisRefinement` proves scoped correspondence for finite recursive semantic case expansion: concrete recursive matching, completion, redundancy, and bounded counterexample witnesses agree with `Oak.PatternAnalysis`. Open scalar domains and representation-level extraction from Go maps remain outside this scoped **R** claim. |
| GADT-style refinements | ✓ | partial | ✓ | ✓ | ✓ |  | canonical `=> EnclosingADT[indices]` constructor results are parsed and checked; fixed atomic indices and repeated result parameters generate equality obligations, restrict reachable constructors, and enter reachable-arm refinement facts. `Oak.GADTRefinement` proves fixed equality, mismatch, repeated-parameter, arity, and reachable-case laws. Nested applied indices, general propositions/existentials, payload-wide substitution, and implementation refinement remain pending |
| Generic constraints/interfaces | ✓ | ✓ | ✓ | partial | partial | partial | static predicate semantics; named requirements may be method interfaces or semantic record shapes; record-shape call inference/discharge/substitution and accumulated multi-variable equality inference have scoped refinement proofs, but constraint sets, function types and method-interface discharge are not yet refined |
| Phantom types | ✓ | partial | partial | ✓ | ✓ |  | `Oak.PhantomRepresentation` proves phantom rebinding changes static identity while preserving the entire runtime representation record, including size, alignment, and bit width; implementation refinement/inference pending |
| Views / spans | ✓ | ✓ | ✓ | ✓ | ✓ | partial | `Oak.Borrowing` proves local read/write authority laws. `Oak.BorrowRegions` proves half-open region symmetry/disjointness, adjacency, zero-length behavior, and conservative unknown-region conflict. Derived slices/subslices retain exact absolute owner regions when statically known; writable children suspend their parent span until the last live child's lexical release, and sibling reborrows coexist when their regions are statically proven pairwise disjoint (fail-closed for unknown regions). `Oak.Reborrow` proves parent/child writable exclusivity and restoration, and `Oak.Reborrow.Split` proves sibling admission requires pairwise disjointness, preserves it, rejects overlap, and restores the parent after the last release, with `Oak.BorrowRegions.Disjoint` as the single authoritative disjointness fact. `Oak.ReborrowRefinement` proves the concrete compiler decision procedure (`regionEnd`, `regionsOverlap`, `admitReborrow`, kept as line-for-line transliterations, cross-checked by differential element-semantics tests) decides exactly the abstract overlap/admission laws on validated regions and fails closed for unknown, malformed, and overflowing regions. **R is scoped to this pure admission procedure**; traversal, borrow-state bookkeeping, and the remaining view/span machinery are not yet refined |
| Borrow-state machine | ✓ | partial | partial | ✓ | ✓ |  | explicit actions; valid transitions preserve state invariant and read/write authority stays exclusive |
| Borrow diagnostics | ✓ | partial | ✓ | ✓ | ✓ |  | `OAK-B0101`..`OAK-B0108` cover borrow reassignment, owner-use/write conflicts, view/span exclusivity, writable-region overlap/unknown-disjointness, use of a writable parent suspended by live reborrows, and sibling reborrows that overlap or cannot be proven disjoint. Borrow provenance records the creating source expression; conflicts select earliest causal source context deterministically and explain known regions or fail-closed unknown regions. `Oak.Borrowing`, `Oak.BorrowRegions`, and `Oak.Diagnostics` prove the corresponding abstract authority/region/diagnostic structural laws. Escape/move diagnostics, remaining borrow builtin errors, canonical byte-location threading, and implementation refinement remain pending |
| Unsafe boundary | ✓ | partial | partial |  |  |  | unsafe must admit assumptions, not disable all checking |
| Effects | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR implements broad/scoped effect identity and conflict validation; `Oak.Effects` proves the abstract subsumption/overlap laws; refinement pending |
| Arena semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR represents explicit arena identity/lifetime; `Oak.RegionLifetime` proves lifetime containment, transitivity, alive-child implies alive-region, and that a region-bound value cannot remain alive after the region ends; refinement pending |
| Slab allocator semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR validates explicit bounded slab/pool capacity and identity; `Oak.Slab` proves abstract capacity preservation; refinement pending |
| Generational handles | ✓ |  |  | ✓ | ✓ |  | `Oak.Handles` proves stale handles cannot resolve after generation-changing reuse and cleared slots never resolve |
| UTF-8 `string` validity | ✓ | partial | partial |  |  |  | legacy string code exists but must reconcile validation invariant |
| UTF-16 / UTF-32 encoded views | ✓ | partial | partial |  |  |  | legacy library/spec work exists; no proof yet |
| Compile-time metadata | ✓ | partial | partial |  |  |  | legacy backtick syntax is not yet normative |
| C backend | ✓ | ✓ | ✓ |  |  |  | semantic shape constraints erase; concrete struct lowering requires resolved representation; golden corpus currently has known stale/missing debt |
| Functional generic specialization | ✓ | partial | partial | ✓ | ✓ | partial | `Oak.GenericConstraintRefinement` proves direct/unary inference, accumulated multiple-variable and multiple-parameter bindings, repeated-occurrence consistency, binary generic applications, result substitution, and scoped record-shape discharge. Constraint sets, deeper applications, refinements and function-type inference remain pending |
| Closure capture/storage effects | ✓ |  |  |  |  |  | semantics specified; implementation pending |
| Protocol/typestate semantic axis | direction |  |  |  |  |  | will receive its own normative spec before implementation |

## Formal verification gate

`spec/lean` is pinned to Lean 4.33.1 and built by `.github/workflows/formal.yml`.

The formal gate currently checks:

- `Oak.TypeLattice`
- `Oak.Effects`
- `Oak.Borrowing`
- `Oak.BorrowRegions`
- `Oak.Reborrow`
- `Oak.ReborrowRefinement`
- `Oak.Handles`
- `Oak.Slab`
- `Oak.Exhaustiveness`
- `Oak.PatternAnalysis`
- `Oak.PatternAnalysisRefinement`
- `Oak.GADTRefinement`
- `Oak.SourcePosition`
- `Oak.Delimited`
- `Oak.RegionLifetime`
- `Oak.PhantomRepresentation`
- `Oak.Layout`
- `Oak.RecordLayout`
- `Oak.RecordShape`
- `Oak.RecordShapeRefinement`
- `Oak.GenericConstraintRefinement`
- `Oak.RepresentationPolymorphism`
- `Oak.TypeVarIdentity`
- `Oak.GeneralizationSafety`
- `Oak.Diagnostics`

A green Lean build means the stated theorems type-check against the pinned proof kernel. It does **not** imply implementation refinement except where an explicit refinement theorem is identified in this matrix.

## Immediate formal-verification queue

1. extend general inference refinement from accumulated equality solving to multiple simultaneous constraint obligations, deeper generic applications, function types and refinement propositions;
2. connect ownership/effect/region analysis to `GeneralizationFacts`, then prove/refine the concrete generalization decision against `Oak.GeneralizationSafety`;
3. finish migrating parser/type/effect/representation and remaining borrow/escape/move failures to first-class diagnostic codes and canonical byte locations, then refine the concrete diagnostic identity/primary-cause operations against `Oak.Diagnostics`;
4. explicit refinement from selected/resolved struct representation to `Oak.RecordLayout` and from `RepresentationRegistry` selection to `Oak.RepresentationPolymorphism`;
5. explicit implementation refinements for type lattice, effects, borrowing/regions, source positions, delimited parsing, region lifetimes, phantom representation, binder identity, and layout normalization;
6. connect the Go coverage-map and indexed-ADT solver representations to `Oak.PatternAnalysisRefinement` and `Oak.GADTRefinement`, then formalize method-interface constraint discharge and its no-runtime-object specialization semantics;
7. formalize additional resource/boundedness laws as the implementation surfaces stabilize;
8. add ABI-specific representation profiles only when an actual backend requires semantics beyond the natural ordered profile.

## Refinement policy

Do not mark a feature **R** merely because Go/Zig tests mirror theorem examples.

`R` requires an explicit formal relation between concrete implementation state/operations and the formal model, with preservation proved by the proof system.
