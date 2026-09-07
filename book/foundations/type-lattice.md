# The Type Lattice

Oak's types form a bounded lattice: `never` at the bottom, `any` at the
top, with join (`|` in the semantic sense, least upper bound) and meet
(`&`, greatest lower bound) defined for every pair. This is not decoration
— the checker's subtype procedure is a concrete DNF (disjunctive normal
form) algorithm, and it carries one of the strongest claims in the
repository: `Oak.TypeLatticeRefinement` proves the implementation **sound
and complete** against the free distributive lattice semantics (an R row
in `docs/spec/STATUS.md`, scoped to the lattice decision procedure over
opaque atoms).

```
                         any
            ┌─────────────┼──────────────┐
        machine ints   nominal islands  shapes
      i8..i64 u8..u64   records, ADTs,  semantic records,
      (exact widths,    simd.U8x16,     record-shape
       explicit         c.Int32,        constraints
       conversions)     Str[E]          (structural)
            └─────────────┼──────────────┘
                         never
```

## Reading the lattice

- **`never`** is the empty type: the type of an impossible match arm, of a
  diverging expression. A redundant arm's body types as `never` and cannot
  widen a match result — impossibility is not allowed to leak.
- **`any`** is the top: everything joins into it, nothing useful comes
  back out without evidence. Oak has no implicit downcasts.
- **Machine integers** are exact-width islands. Movement between them is
  the explicit conversion family of `docs/spec/20-types.md` §11.1 —
  widening constructors, `trunc`/`saturating`/`checked` narrowing,
  same-width `bits` reinterpretation — every operation total, none
  implicit. `Oak.CInterop` proves the boundary rows are lossless
  round-trips.
- **Nominal islands**: declared records, ADTs and their monomorphized
  instantiations (`Option_i32` is a distinct nominal type from
  `Option_u8` — `Oak.Monomorphization` proves instantiation preserves the
  dispatch structure), vectors, and the foreign `c.*` types, which are
  deliberately *unrelated* to the Oak integers so that ABI crossings are
  visible.
- **Shapes** are the structural stratum: a semantic record type used as a
  constraint (`fn length2[T: XY]`) demands fields, not identity —
  `Oak.RecordShapeRefinement` proves the satisfaction procedure equivalent
  to the abstract shape semantics.

## Joins and meets in practice

Match arms join: a match's type is the join of its reachable arms, which
is why an arm of `never` (redundant, impossible) contributes nothing.
Constraints meet: `T: Reader & Writer` is a meet of requirements. The DNF
procedure normalizes both directions, and the proof says the normalization
preserves denotation — accepted subtypings hold under every atom
valuation, rejected ones have a countermodel.

## What the lattice is *not*

There is no subtype relationship between nominal islands (no record
inheritance, no ADT widening), no implicit numeric promotion across
signedness, and no `null` anywhere in the order — absence is an ADT
(`Option[T]`), which the lattice sees as just another nominal sum.
Phantom parameters (`Str[Utf8]` vs `Str[Ascii]`) change static identity
without changing representation (`Oak.PhantomRepresentation`), so the
lattice can distinguish what the machine deliberately cannot.
