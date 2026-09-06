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
| First-class diagnostics | ✓ | partial | ✓ | ✓ | ✓ |  | `diagnostic.Diagnostic` now has stable code/category, one primary label, secondary labels, structured notes/help, deterministic plain rendering, and validation; `Compilation.Check` preserves structured type diagnostics instead of flattening them; generic constraint/record-shape failures use specific codes and explain inferred types/missing fields; `source.Location` establishes canonical source identity. `Oak.Diagnostics` proves retitling/advice/secondary context preserve stable identity and primary cause. Parser/general type/borrow/effect diagnostics, canonical byte-location threading into every diagnostic, code-frame rendering, cascade suppression, and implementation refinement remain pending |
| Delimited parser cursor contract | ✓ | ✓ | ✓ | ✓ | ✓ |  | one `parseDelimited[T]` path covers invocations, parameters, type arguments, and array elements; `Oak.Delimited` proves canonical opener/body/close structure, item preservation, unique close suffix, exact close offset, and trailing-separator semantic transparency; refinement pending |
| Type lattice (`never`, `any`, join/meet) | ✓ | ✓ | ✓ | ✓ | ✓ |  | Go subtype decision procedure is aligned with the proved distributive-lattice laws; explicit implementation refinement is still pending |
| Type inference | ✓ | partial | partial | partial | partial | partial | Oak uses unification/type-scheme machinery where useful but inference is layered with constraints, refinements, ownership/effects/regions, representation and proof obligations. Binder identity is distinct from source-facing names; `Oak.TypeVarIdentity` proves substitution isolation for same-named distinct binders. `Oak.GenericConstraintRefinement` proves scoped direct/unary constrained inference paths. Principal/general inference, richer refinements and exported-signature checking remain pending |
| Polymorphic generalization safety | ✓ | partial | ✓ | ✓ | ✓ |  | `GeneralizeWithFacts` keeps inferred monotypes unchanged while blocking universal quantification when mutable, unique, region, external, effectful, unsafe, or unresolved authority is present. `Oak.GeneralizationSafety` proves safe facts permit generalization and each modeled authority barrier blocks it. Producing these facts automatically from ownership/effect/region analysis and implementation refinement remain pending |
| Semantic records/products | ✓ | ✓ | ✓ |  |  |  | plain `{ ... }` is parsed as a semantic product and projects semantic fields while leaving representation unspecified; source order is preserved as declaration metadata; duplicate fields are rejected |
| Record shape constraints | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | `Oak.RecordShapeRefinement` proves the concrete name-lookup/exact-type decision procedure equivalent to `Oak.RecordShape.Satisfies`. `Oak.GenericConstraintRefinement` additionally proves the implemented direct `T: Shape` call path and one unary-container inference path succeed exactly when the abstract shape obligation holds and return exactly the substituted semantic result. **R is scoped to these modeled record-shape paths**, not arbitrary inference programs or method-interface constraints. |
| Representation polymorphism | ✓ | ✓ | ✓ | ✓ | ✓ |  | `RepresentationRegistry` permits multiple named representation bindings for one semantic definition; selection rebinds only `Definition.Representation`; ordinary resolved record representations must cover semantic fields exactly once. `Oak.RepresentationPolymorphism` proves semantic identity and shape satisfaction are representation-independent; registry implementation refinement pending |
| Natural struct representation selection | ✓ | ✓ | ✓ |  |  |  | parser preserves `struct { ... }` distinctly from `{ ... }`; `type = struct { ... }` selects `RepresentationRecord + natural-ordered` while remaining unresolved until target field representations are known |
| Natural struct layout | ✓ | ✓ | ✓ | ✓ | ✓ |  | `NaturalRecordLayout` computes checked ordered non-packed layout with power-of-two alignment and uint32 overflow rejection; `Oak.RecordLayout` proves identity/order preservation, field alignment, non-overlap, and final-size alignment in the unbounded arithmetic model; implementation refinement pending |
| Record composition | ✓ | partial | partial |  |  |  | semantic composition is separated from subtyping and from representation composition |
| ADTs | ✓ | ✓ | ✓ |  |  |  | old payload/default/tag meanings need compiler reconciliation |
| Pattern matching | ✓ | ✓ | ✓ |  |  |  | canonical `=>`; legacy aliases remain implementation concern |
| Exhaustiveness | ✓ | partial | partial | ✓ | ✓ |  | `Oak.Exhaustiveness` proves wildcard coverage, complete finite constructor coverage, missing-constructor rejection, and monotonicity under added arms; implementation refinement pending |
| GADT-style refinements | direction |  |  |  |  |  | semantic direction specified; surface syntax intentionally not frozen |
| Generic constraints/interfaces | ✓ | ✓ | ✓ | partial | partial | partial | static predicate semantics; named requirements may be method interfaces or semantic record shapes; record-shape call inference/discharge/substitution has a scoped refinement proof, but arbitrary multi-variable/multi-parameter unification and method-interface discharge are not yet refined |
| Phantom types | ✓ | partial | partial | ✓ | ✓ |  | `Oak.PhantomRepresentation` proves phantom rebinding changes static identity while preserving the entire runtime representation record, including size, alignment, and bit width; implementation refinement/inference pending |
| Views / spans | ✓ | ✓ | ✓ | ✓ | ✓ |  | `Oak.Borrowing` proves the local authority-state laws; compiler correspondence is not yet proved |
| Borrow-state machine | ✓ | partial | partial | ✓ | ✓ |  | explicit actions; valid transitions preserve state invariant and read/write authority stays exclusive |
| Unsafe boundary | ✓ | partial | partial |  |  |  | unsafe must admit assumptions, not disable all checking |
| Effects | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR implements broad/scoped effect identity and conflict validation; `Oak.Effects` proves the abstract subsumption/overlap laws; refinement pending |
| Arena semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR represents explicit arena identity/lifetime; `Oak.RegionLifetime` proves lifetime containment, transitivity, alive-child implies alive-region, and that a region-bound value cannot remain alive after the region ends; refinement pending |
| Slab allocator semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR validates explicit bounded slab/pool capacity and identity; `Oak.Slab` proves abstract capacity preservation; refinement pending |
| Generational handles | ✓ |  |  | ✓ | ✓ |  | `Oak.Handles` proves stale handles cannot resolve after generation-changing reuse and cleared slots never resolve |
| UTF-8 `string` validity | ✓ | partial | partial |  |  |  | legacy string code exists but must reconcile validation invariant |
| UTF-16 / UTF-32 encoded views | ✓ | partial | partial |  |  |  | legacy library/spec work exists; no proof yet |
| Compile-time metadata | ✓ | partial | partial |  |  |  | legacy backtick syntax is not yet normative |
| C backend | ✓ | ✓ | ✓ |  |  |  | semantic shape constraints erase; concrete struct lowering requires resolved representation; golden corpus currently has known stale/missing debt |
| Functional generic specialization | ✓ | partial | partial | ✓ | ✓ | partial | `Oak.GenericConstraintRefinement` proves direct and one-level unary inference, substitution through the result type, constraint discharge, and rejection of unsatisfied record shapes. General inference refinement for multiple variables, repeated occurrences, multiple parameters, generic applications, refinements and functions remains pending |
| Closure capture/storage effects | ✓ |  |  |  |  |  | semantics specified; implementation pending |
| Protocol/typestate semantic axis | direction |  |  |  |  |  | will receive its own normative spec before implementation |

## Formal verification gate

`spec/lean` is pinned to Lean 4.33.1 and built by `.github/workflows/formal.yml`.

The formal gate currently checks:

- `Oak.TypeLattice`
- `Oak.Effects`
- `Oak.Borrowing`
- `Oak.Handles`
- `Oak.Slab`
- `Oak.Exhaustiveness`
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

1. extend general inference refinement from direct/one-level unary `T: Shape` calls to multiple parameters, repeated type-variable occurrences, generic applications, multiple quantified variables and refinement obligations;
2. connect ownership/effect/region analysis to `GeneralizationFacts`, then prove/refine the concrete generalization decision against `Oak.GeneralizationSafety`;
3. migrate parser/type/borrow/effect/representation failures to first-class diagnostic codes and canonical byte locations, then refine the concrete diagnostic identity/primary-cause operations against `Oak.Diagnostics`;
4. explicit refinement from selected/resolved struct representation to `Oak.RecordLayout` and from `RepresentationRegistry` selection to `Oak.RepresentationPolymorphism`;
5. explicit implementation refinements for type lattice, effects, borrowing, exhaustiveness, source positions, delimited parsing, region lifetimes, phantom representation, binder identity, and layout normalization;
6. formalize method-interface constraint discharge and its no-runtime-object specialization semantics;
7. formalize additional resource/boundedness laws as the implementation surfaces stabilize;
8. add ABI-specific representation profiles only when an actual backend requires semantics beyond the natural ordered profile.

## Refinement policy

Do not mark a feature **R** merely because Go/Zig tests mirror theorem examples.

`R` requires an explicit formal relation between concrete implementation state/operations and the formal model, with preservation proved by the proof system.
