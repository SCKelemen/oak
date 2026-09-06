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
| Type inference | ✓ | partial | partial | partial | partial | partial | Oak uses unification/type-scheme machinery where useful but inference is layered with constraints, refinements, ownership/effects/regions, representation and proof obligations. Binder identity is distinct from source-facing names; `Oak.TypeVarIdentity` proves substitution isolation for same-named distinct binders. `Oak.GenericConstraintRefinement` proves scoped direct/unary constrained inference. Go tests cover accumulated multi-parameter, repeated-binder and generic-application equality solving; explicit implementation correspondence for those broader paths remains pending. Principal/general inference, richer refinements and exported-signature checking also remain pending |
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
| Generic constraints/interfaces | ✓ | ✓ | ✓ | partial | partial | partial | static predicate semantics; named requirements may be method interfaces or semantic record shapes; record-shape call inference/discharge/substitution has a scoped refinement proof. Accumulated multi-variable equality inference is implemented and tested but not yet explicitly related to the formal model; constraint sets, function types and method-interface discharge are also not yet refined |
| Phantom types | ✓ | partial | partial | ✓ | ✓ |  | `Oak.PhantomRepresentation` proves phantom rebinding changes static identity while preserving the entire runtime representation record, including size, alignment, and bit width; implementation refinement/inference pending |
| Views / spans | ✓ | ✓ | ✓ | ✓ | ✓ | partial | `Oak.Borrowing` proves local read/write authority laws. `Oak.BorrowRegions` proves half-open region symmetry/disjointness, adjacency, zero-length behavior, and conservative unknown-region conflict. Derived slices/subslices retain exact absolute owner regions when statically known; writable children suspend their parent span until the last live child's lexical release, and sibling reborrows coexist when their regions are statically proven pairwise disjoint (fail-closed for unknown regions). `Oak.Reborrow` proves parent/child writable exclusivity and restoration, and `Oak.Reborrow.Split` proves sibling admission requires pairwise disjointness, preserves it, rejects overlap, and restores the parent after the last release, with `Oak.BorrowRegions.Disjoint` as the single authoritative disjointness fact. `Oak.ReborrowRefinement` proves the concrete compiler decision procedure (`regionEnd`, `regionsOverlap`, `admitReborrow`, kept as line-for-line transliterations, cross-checked by differential element-semantics tests) decides exactly the abstract overlap/admission laws on validated regions and fails closed for unknown, malformed, and overflowing regions. **R is scoped to this pure admission procedure**; traversal, borrow-state bookkeeping, and the remaining view/span machinery are not yet refined |
| Borrow-state machine | ✓ | partial | partial | ✓ | ✓ |  | explicit actions; valid transitions preserve state invariant and read/write authority stays exclusive |
| Borrow diagnostics | ✓ | partial | ✓ | ✓ | ✓ |  | `OAK-B0101`..`OAK-B0108` cover borrow reassignment, owner-use/write conflicts, view/span exclusivity, writable-region overlap/unknown-disjointness, use of a writable parent suspended by live reborrows, and sibling reborrows that overlap or cannot be proven disjoint. Borrow provenance records the creating source expression; conflicts select earliest causal source context deterministically and explain known regions or fail-closed unknown regions. `Oak.Borrowing`, `Oak.BorrowRegions`, and `Oak.Diagnostics` prove the corresponding abstract authority/region/diagnostic structural laws. The compile pipeline (`Compilation.Check`) gates on borrow diagnostics: no C is emitted for programs with borrow errors, and the strict profile also rejects recorded warnings. `OAK-B0109` rejects function signatures returning a view/span (the conservative escape rule of `50-borrowing` §5); `Oak.Escape` proves scope exit preserves owner liveness, an escaping borrow of a scope-local owner dangles, and escapes of longer-lived owners are the sound headroom future region-indexed signatures can claim. Move/consume is a recorded design decision (`50-borrowing` §8): v1 owned aggregates are explicit-cost copies, so use-after-move cannot occur until resource types land (`OAK-B0111` reserved). Remaining borrow builtin errors, canonical byte-location threading, and implementation refinement remain pending |
| Unsafe boundary | ✓ | partial | ✓ | ✓ | ✓ |  | unsafe admits assumptions, it does not disable checking: the borrow checker now checks unsafe bodies (previously skipped entirely) and admits exactly the writable-disjointness obligation inside an unsafe boundary, recording each admission as an auditable `OAK-B0110` warning with regional context; all other borrow invariants remain hard errors and the admission is lexically scoped. `Oak.Unsafe` proves safe code admits nothing, the assumption discharges only its own obligation, and exit ends admission. Raw-pointer authority, additional assumption kinds, and refinement pending |
| Effects | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR implements broad/scoped effect identity and conflict validation; `Oak.Effects` proves the abstract subsumption/overlap laws; refinement pending |
| Arena semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR represents explicit arena identity/lifetime; `Oak.RegionLifetime` proves lifetime containment, transitivity, alive-child implies alive-region, and that a region-bound value cannot remain alive after the region ends; refinement pending |
| Slab allocator semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR validates explicit bounded slab/pool capacity and identity; `Oak.Slab` proves abstract capacity preservation; refinement pending |
| Generational handles | ✓ | partial | ✓ | ✓ | ✓ |  | `Oak.Handles` proves stale handles cannot resolve after generation-changing reuse and cleared slots never resolve. `semir.HandleTable` implements slot+generation identity as a transliteration of the model's `Resolves`/`clear`/`reuse` operations (generation advances before re-occupancy; an exhausted 32-bit generation retires its slot fail-closed instead of wrapping), with tests mirroring the proven laws; surface syntax, codegen lowering, and refinement pending |
| UTF-8 `string` validity | ✓ | partial | ✓ | ✓ | ✓ |  | source ingestion is the authoritative validity gate: `source.ValidateUTF8` (a transliteration of `Oak.Utf8Validity.Seq`, Unicode Table 3-7) rejects invalid source before scanning, so string literals cannot carry invalid bytes into `string` values or generated C; differentially tested against the standard library (exhaustive 1–2 byte, bracket-boundary 3–4 byte, randomized). `Oak.Utf8Validity` proves accepted sequences denote Unicode scalars (no surrogates, ≤ U+10FFFF), byte counts equal canonical widths (no overlongs, tied to `Oak.SourcePosition.utf8Width`), and ASCII/compositional validity. Encoding-phantom `Str[E]` types are implemented for static identity: `string = Str[Utf8]`, `Str[Ascii]`/`Str[Utf16]`/`Str[Utf32]` are statically distinct, all lower to one C representation, and `rune` is canonically `u32` end to end. `Oak.StrEncoding` proves retagging preserves units exactly, retyping into utf8 is exactly a validity proof (unvalidated `from_bytes` has no well-formed image), and `Ascii → Utf8` is the one validity-preserving widening. The validated `[]u8 → string` conversion surface (needs `Result`), Utf16/Utf32 code-unit array types, the `rune` range refinement, and refinement remain pending |
| UTF-16 / UTF-32 encoded views | ✓ | partial | partial |  |  |  | legacy library/spec work exists; no proof yet |
| Compile-time metadata | ✓ | partial | partial |  |  |  | legacy backtick syntax is not yet normative |
| C backend | ✓ | ✓ | ✓ |  |  |  | semantic shape constraints erase; concrete struct lowering requires resolved representation. The golden corpus (single authoritative case list in `serialize.GoldenCases`) captures every stage — source through emitted C — for all cases, is verified by `go test` (drift fails CI), and each golden `.c` is syntax-checked with the system C compiler; corpus covers block bodies, tail-recursion loop lowering, and unsafe admission. Legacy ADT value-tag syntax (`Ok: 200`) fails to parse and is captured as an error-path case pending ADT reconciliation |
| Functional generic specialization | ✓ | partial | partial | ✓ | ✓ | partial | `Oak.GenericConstraintRefinement` proves direct/unary inference, result substitution, and scoped record-shape discharge. Go implements and tests accumulated multiple-variable/parameter bindings, repeated-occurrence consistency, and generic applications, but their explicit refinement proof remains pending alongside constraint sets, refinements and function types |
| Closure capture/storage effects | ✓ | partial | ✓ | ✓ | ✓ |  | capture analysis runs on every function literal: captureless literals are legal code pointers; capturing closures are rejected (`OAK-T0401`, listing the captured names) until environment storage can be justified explicitly — capturing never silently heap-promotes and the backend never silently drops an environment. `Oak.ClosureCapture` proves captureless closures escape freely, stack environments cannot outlive their frame, and non-escaping stack capture is safe (the future storage-surface headroom). Storage justification surfaces, codegen lambda lifting for captureless literals, and generalization-facts integration pending |
| Discipline profile (bounded execution) | ✓ | partial | ✓ | ✓ | ✓ |  | `docs/spec/85-discipline.md` defines MISRA/Power-of-Ten/TigerStyle profiles. Safe recursion is enforced: the `discipline` analyzer ranks call-graph SCCs (strict rank decrease on stack calls, non-increase on tail calls), rejects stack-consuming cycles (`OAK-D0101`), records unlowered tail cycles (`OAK-D0102`, warning), and the C backend compiles self tail recursion to loops — including terminating recursion whose base cases sit in lowerable-shape match arms (identifier scrutinee, literal/wildcard patterns), emitted as guarded returns and same-signature mutual tail cycles to trampolines (one state-machine engine per cycle, one frame, thin wrappers; analyzer and backend share the `TrampolineLowerable` decision procedure so no cycle is accepted as lowered without being lowered). `Oak.Discipline` proves the rank certificate bounds stack depth and forces cycles to be tail-only. `OAK-D0102` remains for mismatched-signature groups, binding/variant-pattern arms, and non-identifier scrutinees; `discipline.LowerableMatchShape` is the single shape authority shared with the backend. The `assert` builtin is implemented end to end (typechecked Bool condition, interpreter check, always-on C lowering via `__builtin_trap`, never elided). Bounded loops, allocation-phase, assertion-density, and checked-result rules are specified direction; the pipeline gates on discipline errors (and, in the strict profile, warnings). Bounded loops are enforced: the canonical counter shape is recognized (`Oak.BoundedLoop` proves its static iteration bound) and every other `while` records `OAK-D0103`, which strict rejects. Allocation-phase enforcement and refinement pending |
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
- `Oak.Escape`
- `Oak.Unsafe`
- `Oak.Discipline`
- `Oak.Utf8Validity`
- `Oak.StrEncoding`
- `Oak.ClosureCapture`
- `Oak.BoundedLoop`
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

1. relate the concrete accumulated substitution/composition algorithm to a normalized formal solver (including metavariable chains), then extend it to simultaneous constraint obligations, deeper generic applications, function types and refinement propositions;
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
