# Oak Language Specification

This directory is the **normative specification** of Oak.

Older top-level design documents remain valuable design history and implementation notes, but they are not authoritative when they disagree with this directory. A legacy document is retired only after its useful decisions have been reconciled here.

## Language priorities

Oak optimizes for, in order:

1. **Correctness**
2. **Performance**
3. **Simplicity**

Safety and ergonomics are cross-cutting constraints.

The language should have a tight, lightweight, orthogonal surface. Prefer composition from a small number of powerful constructs—records, ADTs/GADT-style refinements, functions, generics, pattern matching, ownership/effects, and ordinary library types—over domain-specific syntax.

## Specification layers

Every feature may have up to five linked layers:

```text
surface syntax
    ↓
static semantics
    ↓
dynamic / machine semantics
    ↓
formal model + theorems
    ↓
implementation correspondence
```

A feature is not called “formally verified” merely because a mathematical model exists. We distinguish specification proof from implementation refinement.

## Verification vocabulary

Use these terms precisely:

- **specified** — normative syntax and semantics exist;
- **implemented** — compiler/runtime behavior exists;
- **tested** — executable implementation tests cover stated properties;
- **modeled** — a machine-checkable formal model exists;
- **proved** — stated theorem/invariant is mechanically checked in the formal model;
- **refined** — an explicit machine-checked correspondence connects implementation representation/operations to the formal model.

## Authoritative documents

- `00-constitution.md` — values, design constraints, semantic axes
- `05-ergonomics-and-cost.md` — functional ergonomics and systems cost transparency
- `10-syntax.md` — lexical/layout/block rules and canonical punctuation
- `15-diagnostics.md` — first-class compiler errors, stable codes, causal labels, notes/help, and UX requirements
- `20-types.md` — type universe, subtyping, joins/meets, nominal identity
- `25-type-inference.md` — layered local inference, safe generalization, explicit module/API contracts
- `30-adts-patterns.md` — ADTs, GADT direction, constructors, matching, exhaustiveness
- `40-records.md` — products, record identity, composition, order, layout separation
- `45-representations.md` — multiple checked representations per semantic type and representation selection
- `50-borrowing.md` — ownership, views, spans, safe/unsafe boundaries
- `60-effects-allocation.md` — effects, arenas, slabs, handles, realtime prohibitions
- `70-strings.md` — encoded text, validation, borrowing and representation
- `80-metadata.md` — typed attributes/tags and phantom semantic types
- `90-backend.md` — executable lowering and C-backend requirements
- `STATUS.md` — implementation and proof coverage matrix

The files above are introduced incrementally. Until a feature has an authoritative document here, its legacy document remains design input rather than normative law.

## Formal verification layout

```text
spec/
  lean/
    Oak/
      TypeLattice.lean
      Effects.lean
      Borrowing.lean
      Diagnostics.lean
      ...
  tla/
    ...
```

Lean is the primary proof layer for local algebraic and semantic laws: type lattices, refinements, effect subsumption, bounds, ownership facts, representation-independent compiler invariants, and structural diagnostic invariants.

TLA+ (or another explicit state-machine model checker) is appropriate when the property is fundamentally temporal/concurrent: ownership transfer across actors, asynchronous protocols, scheduler/queue interaction, or other behavior over traces.

## Proof/code relationship

The default maturity path is:

```text
normative spec
    ↓
Lean/TLA+ model + proofs
    ↓
implementation property tests against the same laws
    ↓
explicit refinement for load-bearing compiler/runtime components
```

The first refinement targets should be small and foundational: the type lattice, delimited parser cursor contract, borrow-state transitions, effect subsumption, exact source-span conversions, and first-class diagnostic structure.
