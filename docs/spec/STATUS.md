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
| Layout + explicit blocks | ✓ | ✓ | ✓ |  |  |  | parser/layout equivalence exists; formal cursor/layout model pending |
| Source spans / UTF-16 editor positions | ✓ | draft | draft |  |  |  | implementation is in draft PR #6 |
| Delimited parser cursor contract | ✓ | draft | draft |  |  |  | implementation is in draft PR #6; formal cursor proof planned |
| Type lattice (`never`, `any`, join/meet) | ✓ | ✓ | ✓ | planned in this branch | planned |  | current `IsSubtype` intersection law needs reconciliation |
| Nominal records | ✓ | ✓ | ✓ |  |  |  | ordered field semantics implementation is in draft PR #6 |
| Record composition | ✓ | partial | partial |  |  |  | semantics now separated from subtyping |
| ADTs | ✓ | ✓ | ✓ |  |  |  | old payload/default/tag meanings need compiler reconciliation |
| Pattern matching | ✓ | ✓ | ✓ | planned | planned |  | canonical `=>`; legacy aliases remain implementation concern |
| Exhaustiveness | ✓ | partial | partial | planned | planned |  | finite constructor-set proof target |
| GADT-style refinements | direction |  |  |  |  |  | semantic direction specified; surface syntax intentionally not frozen |
| Generic constraints/interfaces | ✓ | ✓ | ✓ |  |  |  | static predicate semantics; dynamic interface values not core |
| Phantom types | ✓ | partial | partial |  |  |  | zero-runtime representation law to prove |
| Views / spans | ✓ | ✓ | ✓ | planned | planned |  | borrowing implementation/spec reconciliation needed |
| Borrow-state machine | ✓ | partial | partial | planned | planned |  | local formal model planned |
| Unsafe boundary | ✓ | partial | partial |  |  |  | unsafe must admit assumptions, not disable all checking |
| Effects | ✓ | draft | draft | planned | planned |  | parameterized effect implementation in draft PR #6 |
| Arena / slab allocator semantics | ✓ | draft | draft |  |  |  | semantic IR in draft PR #6; surface library types pending |
| Generational handles | ✓ |  |  | planned | planned |  | semantics only; implementation representation not stabilized |
| UTF-8 `string` validity | ✓ | partial | partial |  |  |  | legacy string code exists but must reconcile validation invariant |
| UTF-16 / UTF-32 encoded views | ✓ | partial | partial |  |  |  | legacy library/spec work exists; no proof yet |
| Compile-time metadata | ✓ | partial | partial |  |  |  | legacy backtick syntax is not yet normative |
| C backend | ✓ | ✓ | ✓ |  |  |  | golden corpus currently has known stale/missing debt |
| Functional generic specialization | ✓ | partial | partial |  |  |  | no-hidden-dispatch/boxing law needs tests/proofs |
| Closure capture/storage effects | ✓ |  |  |  |  |  | semantics specified; implementation pending |
| Protocol/typestate semantic axis | direction |  |  |  |  |  | will receive its own normative spec before implementation |

## Immediate formal-verification queue

1. type-lattice algebra;
2. effect overlap/subsumption;
3. local borrow-state safety;
4. finite ADT exhaustiveness;
5. parser delimited-sequence cursor invariant;
6. source byte-span ↔ UTF-16 coordinate correctness;
7. generational-handle stale-reference theorem;
8. record layout/alignment once target layout representation stabilizes.

## Refinement policy

Do not mark a feature **R** merely because Go/Zig tests mirror theorem examples.

`R` requires an explicit formal relation between concrete implementation state/operations and the formal model, with preservation proved by the proof system.
