# Oak Type System

This document is normative for Oak's type universe and subtyping laws.

## 1. Semantic view

For static reasoning, a type denotes a set/predicate of admissible values. We write `A <= B` when every value admitted by `A` is admitted by `B` without a runtime check.

Subtyping is a partial order over semantic types:

- reflexive: `A <= A`;
- transitive: `A <= B` and `B <= C` imply `A <= C`;
- antisymmetric up to semantic equivalence.

Nominal identity is separate from structural representation. Two named record declarations can have identical fields/layout and still be distinct nominal types.

## 2. Bottom, unit, and top

### `never`

`never` has no inhabitants and is bottom:

```text
never <= T
```

for every type `T`.

It is the result type of computations that cannot return normally.

### `()` / Unit

Unit has exactly one semantic value. `()` is the canonical surface spelling.

An empty record value/type may have the same zero-field representation, but representation equality does not by itself create nominal type equality.

### `any`

`any` is a restricted top type:

```text
T <= any
```

for every type `T`.

Using `any` as a runtime value requires an explicit dynamic representation strategy. The type checker must not silently introduce boxing, allocation, RTTI, or hidden runtime type tags merely because `any` appears in a static lattice computation.

Typecase patterns over a runtime `any` are therefore **not part of the core language until that representation is specified explicitly**.

## 3. Joins and meets

The semantic join `A join B` is the least type containing both; the semantic meet `A meet B` is the greatest type contained by both.

Required laws include:

```text
A <= A join B
B <= A join B

A meet B <= A
A meet B <= B

join/meet are commutative
join/meet are associative
join/meet are idempotent

A join never = A
A meet any    = A
A join any    = any
A meet never  = never

A join (A meet B) = A
A meet (A join B) = A
```

The compiler may canonicalize joins/meets internally. Surface syntax need not expose arbitrary union/intersection values merely because the checker uses these operations.

## 4. ADTs are tagged sums, not ordinary union values

An Oak declaration such as:

```oak
Option[T]: type =
  | Some: T
  | None
```

defines one **nominal tagged sum type** `Option[T]` with constructors `Some` and `None`.

The `|` in an ADT declaration enumerates constructors. It does not mean that `Option[T]` is an untagged runtime union of `T` and Unit, nor does it grant arbitrary implicit conversion between payload types and the ADT.

Pattern matching can narrow an ADT value to a constructor case because the constructor tag is part of the value's semantics.

## 5. Records are products

A record is an ordered product of named fields:

```oak
Point: type = {
  x: i32
  y: i32
}
```

Source field order is semantically preserved. It may influence an explicitly chosen ABI/layout, formatting, generated schemas, and tooling.

Field order alone does not determine target offsets: size, alignment, padding, packing, and ABI rules belong to the representation axis.

Named records are nominal by default. Equal structure does not imply mutual subtyping.

## 6. Record composition is not subtyping

Definition-time record composition combines fields to form a new nominal product. It is a construction operation, not width subtyping.

If surface `&` is retained for record composition, its meaning is context-specific:

```oak
Point3: type = Point2 & { z: i32 }
```

means “define a new record from these components,” not `Point3 <= Point2`.

Duplicate fields are legal only when their types and required semantic attributes agree exactly; otherwise composition fails.

No automatic structural record subtyping is part of the core language.

## 7. Interface constraints are predicates

An interface constraint describes requirements on a type's operations. It is best understood as a predicate over types, not as a runtime interface object.

```oak
fn copy[T: Reader & Writer](x: T): ()
```

uses `&` as **constraint conjunction**: `T` must satisfy both predicates.

Core Oak interfaces are compile-time constraints and are erased/specialized during executable lowering. Dynamic existential/interface values require a separate explicit feature and representation.

## 8. Phantom types

A type parameter may distinguish semantic identities without changing runtime representation.

```oak
Id[T]: type = u64
```

can make `Id[User]` distinct from `Id[Order]` while both lower to the same machine representation.

Phantom identity belongs to the type axis. It must not silently add runtime fields.

## 9. Refinements and GADT direction

Refinements add propositions to a base type:

```text
{x : u16 | x < N}
```

Exact surface syntax is not yet normative, but the semantic rule is: a refined type denotes the subset of its base type satisfying the proposition.

GADT-style constructors extend the same idea to constructor-specific result refinements. They should be introduced by enriching ADTs and propositions rather than by creating a separate object system.

## 10. Machine types

Fixed-width integer types (`u8`..`u64`, `i8`..`i64`) have exact machine-width semantics. Target-width integer/pointer-sized types are distinct semantic types whose widths are supplied by the target.

Mathematical proof integers are never silently substituted for machine integers. Overflow, conversion, division, and shift semantics must be specified for each machine operation.

## 11. Formal obligations

The executable type lattice must satisfy the laws in §3.

The initial Lean model in `spec/lean/Oak/TypeLattice.lean` proves those laws over semantic type denotations. Go property/unit tests must exercise the implementation against the same laws.

An implementation is not called refined until we explicitly relate `typechecker.Type`/`IsSubtype`/`Join`/`Meet` to the formal denotation model.
