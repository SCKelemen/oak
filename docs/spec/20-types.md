# Oak Type System

This document is normative for Oak's type universe and subtyping laws.

## 1. Semantic view

For static reasoning, a type denotes a set/predicate of admissible values. We write `A <= B` when every value admitted by `A` is admitted by `B` without a runtime check.

Subtyping is a partial order over semantic types:

- reflexive: `A <= A`;
- transitive: `A <= B` and `B <= C` imply `A <= C`;
- antisymmetric up to semantic equivalence.

Semantic type identity is separate from runtime representation. Two types may share an identical machine layout and remain statically distinct; conversely, a semantic type may be useful to checking/proof/tooling without fixing a runtime layout at all.

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

An empty record or zero-sized struct may have the same cardinality/storage size, but representation equality does not create nominal type equality.

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

Pattern matching can narrow an ADT value to a constructor case because constructor identity is part of the value's semantics. Its concrete tag/payload representation is a separate axis.

## 5. Records are semantic products/shapes

A record describes named product semantics:

```oak
XY: type = {
  x: f32
  y: f32
}
```

The abstract record meaning is determined by its named fields and their semantic types. Source declaration order is preserved by the compiler as an authoritative declaration fact for formatting, schemas, documentation and possible representation derivation, but **field order is not itself structural-compatibility semantics**.

Named record types remain nominal in ordinary value positions. Equal field sets do not silently create ordinary subtyping between distinct named types.

A record definition does not promise byte offsets, padding, field alignment, total size, packing, calling convention classification, or any other ABI fact.

This allows a record shape to participate in compile-time reasoning without requiring a runtime representation.

### 5.1 Record shapes as constraints

In a generic constraint position, a record shape may act as a structural predicate over members:

```oak
XY: type = { x: f32, y: f32 }

fn length2[T: XY](value: T): f32
  value.x * value.x + value.y * value.y
```

The intended rule is: `T` satisfies `XY` when it provides fields with the required semantic names/types. This does not require matching memory offsets or an identical layout, and does not create a runtime interface object.

Shape satisfaction is a **constraint relation**, not global width subtyping. Its compiler implementation and formal laws must be completed before this surface use is considered implemented.

### 5.1 Nominal identity of declared structs

A **declared struct** type is a nominal island: two named struct types are
the same type only when they are the same declaration (or the same
template instantiation) — `Idx[Thread]` and `Idx[Timer]` share a shape and
are distinct. This is what makes phantom-parameterized records (typed
indices, tagged handles) sound: the phantom does its work in the name.

The nominal commitment rides on the `struct` keyword, because `struct`
commits to an ordered concrete representation. A **semantic record type**
(`u8_ab: type = { a, b: u8 }`, named or not) remains a structural,
order-free *shape*: any record with those fields satisfies it, including
either ordered struct over them —

```oak
u8_ab: type = { a, b: u8 }             // shape: order-free

AB: type = struct { a: u8, b: u8 }     // ordered layout, nominal
BA: type = struct { b: u8, a: u8 }     // different layout, different type

sum: (v: u8_ab): u8 = v.a + v.b        // AB and BA both satisfy u8_ab
```

`AB` and `BA` never substitute for each other (nominal, and their layouts
differ), but both flow into `u8_ab` positions. Anonymous shapes and shape
*constraints* (§9 of `10-syntax.md`) remain satisfaction checks, not
identity. Grouped field names (`a, b: u8`) declare each name at the shared
type, in written order.

## 6. Structs select runtime product representation

`struct` is the representation-bearing product form:

```oak
Point: type = struct {
  x: f32
  y: f32
}
```

`Point` has record/product semantics and additionally selects concrete ordered struct storage. Plain `struct` selects Oak's natural ordered representation profile unless another explicit representation policy is specified.

Therefore:

```oak
Shape: type = { x: u8, y: u32 }
Stored: type = struct { x: u8, y: u32 }
```

have related semantic field shapes, but only `Stored` makes the ordinary struct layout policy part of its declaration.

A backend may still need target primitive representations before the final offsets/size can be resolved. Selecting a representation policy and resolving all of its numeric layout facts are distinct compiler states.

Future packed, extern, explicit-offset, wire, vector, or platform ABI representations must be explicit representation choices rather than alternate meanings of `{ ... }`.

## 7. Record composition is not subtyping

Definition-time record composition combines fields to form a new semantic product. It is a construction operation, not width subtyping.

If surface `&` is retained for record composition, its meaning is context-specific:

```oak
Point3: type = Point2 & { z: i32 }
```

means “define a new record from these components,” not `Point3 <= Point2`.

Duplicate fields are legal only when their types and required semantic attributes agree exactly; otherwise composition fails.

Composition does not imply that the resulting type has the same runtime representation policy as any component. Representation composition must be established separately.

## 8. Interface constraints are predicates

An interface constraint describes requirements on a type's operations. It is best understood as a predicate over types, not as a runtime interface object.

```oak
fn copy[T: Reader & Writer](x: T): ()
```

uses `&` as **constraint conjunction**: `T` must satisfy both predicates.

Core Oak interfaces are compile-time constraints and are erased/specialized during executable lowering. Dynamic existential/interface values require a separate explicit feature and representation.

Longer term, method/interface requirements and record-shape requirements should share the same constraint machinery where possible rather than creating separate runtime object models.

## 9. Phantom types

A type parameter may distinguish semantic identities without changing runtime representation.

```oak
Id[T]: type = u64
```

can make `Id[User]` distinct from `Id[Order]` while both lower to the same machine representation.

Phantom identity belongs to the type axis. It must not silently add runtime fields.

## 10. Refinements and GADT direction

Refinements add propositions to a base type:

```text
{x : u16 | x < N}
```

A refined type denotes the subset of its base type satisfying the proposition. General value-refinement surface syntax remains future work.

GADT-style constructors extend the same idea to constructor-specific result refinements. Constructor result-index syntax and equality solving are normative in `30-adts-patterns.md`: fixed result indices and repeated result parameters introduce equality propositions. More general propositions must extend this refinement system rather than create a separate object system.

## 11. Machine types

Fixed-width integer types (`u8`..`u64`, `i8`..`i64`) have exact machine-width semantics. Target-width integer/pointer-sized types are distinct semantic types whose widths are supplied by the target.

Mathematical proof integers are never silently substituted for machine integers. Overflow, conversion, division, and shift semantics must be specified for each machine operation.

### 11.0 Const parameters

A generic type may take **value parameters** alongside type parameters,
declared with a fixed-width integer kind and instantiated with integer
literals:

```oak
Ring[T, N: u32]: type = struct {
  buffer: [N]T
  head: u32
  count: u32
}

events: Ring[u8, 8]
```

`N` participates in field types (`[N]T`) and is substituted at
instantiation — `Ring[u8, 8]` is a distinct nominal type whose layout is
computed and proven like any concrete record (`Oak.RecordLayout` and the
emitted `sizeof`/`offsetof` assertions). Template knowledge disambiguates
applications from array syntax, so a const parameter cannot be the sole
argument of an unknown name; `%` is the modulo operator these shapes want.

### 11.1 Explicit integer conversions

Implicit conversion is limited to value-preserving widening within one
signedness (constructor form: `i32(x: i8)`, `u64(x: u32)`; unsigned also
widens into a strictly wider signed type). Every other move between machine
integers is an explicit named conversion, `{target}_{op}_{source}`, and
every operation is **total** with two's-complement semantics — the C
lowering uses no implementation-defined conversions (signed results are
produced by union type punning, defined since C99 TC3):

| Op | Pair rule | Semantics |
| --- | --- | --- |
| `trunc` | strictly narrower, same signedness | low bits, wraps mod `2^N` |
| `saturating` | strictly narrower, same signedness | clamps to the target range |
| `bits` | same width, opposite signedness | bit-pattern reinterpretation (`i32_bits_u32`, `u64_bits_i64`) |
| `checked` | strictly narrower, same signedness | `Result[target, Overflow]` — `Ok` in range, `Err(Overflow)` otherwise; requires the program to declare `Result[T, E]` (Ok/Err) and `Overflow` |

`bits` is the explicit path between `u32` and `i32` that widening and
narrowing deliberately lack: honest at the call site, free at runtime.

### 11.2 Generic functions monomorphize

```oak
max[T]: (a: T, b: T): T {
  a < b ? b | a
}

wide: u64 = max(u64(40), u64(2))     // inferred: max_u64
narrow: u32 = max[u32](2, 40)        // explicit instantiation
```

An UNCONSTRAINED generic function declaration is a template — never
checked or emitted generically. Each call site infers type bindings from
its argument types (bare type-parameter positions bind directly; `[N]T`
positions descend into the element) or supplies them explicitly; the body
is specialized through the single substitution authority
(`SubstituteTypeAST`) and the specialization is typechecked with concrete
types — instantiation-time checking, the record-template precedent: an
operation illegal for the concrete type fails at that instantiation
(`maskLow[T]` using `&` fails for `T = i32`, works for `u32`).

Specializations are appended to the program and templates removed BEFORE
the borrow checker, discipline analysis, lowering, and codegen run: every
safety gate sees only ordinary functions and runs on every instantiation.
Call sites are rewritten to the mangled name (`oak_max_u32`). The
instantiation cache registers before body checking, so recursive generic
functions terminate; generic functions calling generic functions
re-resolve concretely inside the specialized body. Uninferable parameters
demand explicit instantiation; unmangleable arguments fail closed.

Constraint-carrying generics (`fn [T: Position] sum_xy(p: T)`) keep the
structural constraint-checking path and its structured diagnostics
(`OAK-T0104`); their monomorphization is the recorded next step.

## 12. Formal obligations

The executable type lattice must satisfy the laws in §3.

Record/struct verification is split deliberately:

- semantic record proofs cover member uniqueness, shape satisfaction and composition;
- struct representation proofs cover ordered placement, alignment, padding, non-overlap and final size;
- a representation refinement must prove that a concrete `struct` declaration is lowered according to its selected representation policy.

The initial Lean type-lattice model proves its laws over semantic type denotations. Go property/unit tests must exercise the implementation against the same laws.

An implementation is not called refined until we explicitly relate concrete compiler structures/operations to the formal denotation and representation models.
