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
| Layout + explicit blocks | ✓ | ✓ | ✓ |  |  |  | parser/layout equivalence exists; formal layout normalization model pending |
| Source spans / UTF-16 editor positions | ✓ | ✓ | ✓ | ✓ | ✓ |  | `Oak.SourcePosition` proves UTF-8/UTF-16 scalar-width rules, additive coordinate accumulation, monotonic offsets, and ASCII width equivalence; Go tests cover emoji, multiline positions, byte-boundary rejection, links, and LSP coordinates; refinement pending |
| Delimited parser cursor contract | ✓ | ✓ | ✓ | ✓ | ✓ |  | one `parseDelimited[T]` path covers invocations, parameters, type arguments, and array elements; `Oak.Delimited` proves canonical opener/body/close structure, item preservation, unique close suffix, exact close offset, and trailing-separator semantic transparency; refinement pending |
| Type lattice (`never`, `any`, join/meet) | ✓ | ✓ | ✓ | ✓ | ✓ |  | Go subtype decision procedure is aligned with the proved distributive-lattice laws; explicit implementation refinement is still pending |
| Nominal records | ✓ | ✓ | ✓ |  |  |  | authoritative source field order is preserved; duplicate fields are rejected; ABI offsets remain a target-layout concern |
| Record composition | ✓ | partial | partial |  |  |  | semantics now separated from subtyping |
| ADTs | ✓ | ✓ | ✓ |  |  |  | old payload/default/tag meanings need compiler reconciliation |
| Pattern matching | ✓ | ✓ | ✓ |  |  |  | canonical `=>`; legacy aliases remain implementation concern |
| Exhaustiveness | ✓ | partial | partial | ✓ | ✓ |  | `Oak.Exhaustiveness` proves wildcard coverage, complete finite constructor coverage, missing-constructor rejection, and monotonicity under added arms; implementation refinement pending |
| GADT-style refinements | direction |  |  |  |  |  | semantic direction specified; surface syntax intentionally not frozen |
| Generic constraints/interfaces | ✓ | ✓ | ✓ |  |  |  | static predicate semantics; dynamic interface values not core |
| Phantom types | ✓ | partial | partial |  |  |  | zero-runtime representation law to prove |
| Views / spans | ✓ | ✓ | ✓ | ✓ | ✓ |  | `Oak.Borrowing` proves the local authority-state laws; compiler correspondence is not yet proved |
| Borrow-state machine | ✓ | partial | partial | ✓ | ✓ |  | explicit actions; valid transitions preserve state invariant and read/write authority stays exclusive |
| Unsafe boundary | ✓ | partial | partial |  |  |  | unsafe must admit assumptions, not disable all checking |
| Effects | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR implements broad/scoped effect identity and conflict validation; `Oak.Effects` proves the abstract subsumption/overlap laws; refinement pending |
| Arena semantics | ✓ | ✓ | ✓ |  |  |  | Semantic IR represents explicit arena identity/lifetime and validates required metadata; region non-escape proof pending |
| Slab allocator semantics | ✓ | ✓ | ✓ | ✓ | ✓ |  | Semantic IR validates explicit bounded slab/pool capacity and identity; `Oak.Slab` proves abstract capacity preservation; refinement pending |
| Generational handles | ✓ |  |  | ✓ | ✓ |  | `Oak.Handles` proves stale handles cannot resolve after generation-changing reuse and cleared slots never resolve |
| UTF-8 `string` validity | ✓ | partial | partial |  |  |  | legacy string code exists but must reconcile validation invariant |
| UTF-16 / UTF-32 encoded views | ✓ | partial | partial |  |  |  | legacy library/spec work exists; no proof yet |
| Compile-time metadata | ✓ | partial | partial |  |  |  | legacy backtick syntax is not yet normative |
| C backend | ✓ | ✓ | ✓ |  |  |  | golden corpus currently has known stale/missing debt |
| Functional generic specialization | ✓ | partial | partial |  |  |  | no-hidden-dispatch/boxing law needs tests/proofs |
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

A green Lean build means the stated theorems type-check against the pinned proof kernel. It does **not** imply implementation refinement.

## Immediate formal-verification queue

1. region/arena non-escape theorem;
2. phantom-type zero-runtime representation law;
3. record layout/alignment once target layout representation stabilizes;
4. formal layout-normalizer balance/equivalence model;
5. explicit implementation refinements for type lattice, effects, borrowing, exhaustiveness, source positions, and delimited parsing.

## Refinement policy

Do not mark a feature **R** merely because Go/Zig tests mirror theorem examples.

`R` requires an explicit formal relation between concrete implementation state/operations and the formal model, with preservation proved by the proof system.
