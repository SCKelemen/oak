# Typechecker responsibility boundaries (A04)

Inspected baseline: `349fb730` on `specification`. This is a boundary audit and
focused soundness repair, not a claim that the full checker is proved sound.

| Concern | Owner | Contract and forbidden conflation |
| --- | --- | --- |
| Nominal identity | `lattice_identity.go`, resolved struct/ADT names | Lattice atoms use `latticeAtomIdentical`, not `Type.Equals`. Struct names and binder pointers cannot be replaced by printed shapes or labels. |
| Structural compatibility | `RecordType.Equals`, `isAssignable`, `SatisfiesConstraint` in `typechecker.go`; `record_compatibility.go` | Shape satisfaction, directional assignment, and nominal equality are distinct relations. Empty nominal tokens and row openness must be checked before structural equations. |
| Unification | `unification.go` | Solve equations under accumulated substitutions; return nil on failure. Inspect supported composite children before leaf compatibility. Never commit persistent binder state. |
| Binder state | `binder_state.go`; schemes/substitution and generalization in `hm.go`; `type_variables.go` | Pointer identity keys substitution. Successful enclosing expressions commit staged equations; failures discard them. Names remain diagnostic/legacy declaration labels. |
| Effects | `generalization.go` capture/initializer analysis, `scalar_global_writes.go`; compiler effect checking | Evaluating an initializer and executing a captured function body are different events. Effect evidence blocks quantification; it does not create nominal type identity. |
| Authority | `generalization.go`, `resource_flow.go`, `resource_call_exclusivity.go`, `resource_parameter_modes_test.go`, `regions.go` | Mutable/unique/external/region authority survives aliasing and prevents unsafe generalization. Structural compatibility is not permission to consume or borrow a resource. |

The equation solver and binder commits have been extracted from `hm.go` into
separate files in the same package. This is a review boundary, not Go package
encapsulation: package-private code can still call either. Schemes retain
explicit generalization barriers separately from their semantic type.

## Confirmed conflations repaired

1. The record fallback admitted a zero-field nominal struct against a semantic
   empty record despite `Equals` rejecting it. Vacuous field iteration erased
   the nominal token. Repeated-variable equations could consequently accept
   both representations for one binder.
2. The record fallback ignored `Open`. Empty-record compatibility shortcuts
   also bypassed this distinction, including when nested in other types.
3. Function, array, generic and structural-record equality shortcuts could
   bypass child admission. These composites now solve their children first;
   same resolved nominal structs retain name-based identity.
4. Unit was an alternative route around row admission: `Equals` accepted an
   empty open row against Unit, including repeated-binder equations. At record
   equation dispatch only, Unit now has the view of a closed empty semantic
   record. Both operand orders therefore pass through the same nominal/row
   admission and field equations. This does not rewrite stored types, binder
   solutions, `Type.Equals`, or directional constraint satisfaction.

Regressions cover both argument orders, direct records, functions, arrays,
generics, enclosing records, repeated binders, and positive structural cases.
They fail on the baseline. The Unit bypass additionally has parser-produced
open-row regressions, Unit-first three-argument binder bridges, transaction
rollback checks, and a directional constraint-satisfaction control. Existing
compatibility of closed empty semantic records with Unit and of nonempty
structs with semantic shapes remains intentional.

`Oak.RecordUnificationBoundary` proves rejection of unequal rows, distinct
nominal names, and empty nominal/shape crossings in both directions, plus
positive nonempty structural admission. This is a metadata-projection theorem,
not a mechanized refinement proof for Go, source-level preservation/progress,
or the entire unifier. The bounded record/Unit operand view additionally proves
open-row/Unit rejection in both directions and closed-empty-shape/Unit metadata
admission. It does not model field equations, substitution, persistent binder
transactions, or any other type constructor. Existing `TypeVarIdentity`,
`GeneralizationSafety`, and `TypeLatticeAtomIdentity` proofs remain unchanged.

## Prioritized remaining gaps

1. **Finish relation separation:** `Type.Equals` still combines compatibility
   with equality for narrowed ADTs, semantic shapes, and Unit. Audit remaining
   callers before replacing it; changing it globally would silently change
   inference and source compatibility. The unifier still uses it for leaves.
2. **Explicit declaration binders:** inferred schemes carry exact binder lists,
   but explicit legacy schemes and constraints still resolve source labels.
   Migrate constructors and constraint ownership together; reject ambiguous
   independent binders rather than merging by display name.
3. **Effect summaries:** initializer analysis conservatively rejects unknown
   calls. Carry checked summaries through schemes without treating effects as
   nominal identity or confusing deferred bodies with immediate evaluation.
4. **Authority transaction contract:** formalize nested staging, rollback, and
   cross-group escaped-variable commits against the Go heap model. Existing
   tests are not a complete proof of persistent-state isolation.
5. **Composite coverage:** the solver handles functions, records, arrays and
   generics structurally; other constructors rely on leaf compatibility. Audit
   inference under buffers, atomics, C function pointers and narrowed ADTs with
   their distinct authority/ABI obligations before extending decomposition.
6. **Resolved identities:** nominal identity remains a resolved name string;
   preserve module qualification and specialization identity when introducing
   declaration IDs. Do not infer representation/ABI identity from field shape.

No ARM64/RV64 implementation, proof statement, verification gate, or trust
assumption is weakened by this change. Native integration validation remains
necessary because checker admission affects which programs reach backends.
