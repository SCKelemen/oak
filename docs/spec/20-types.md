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

Const parameters also range over **functions**. A type parameter declared
with an integer kind is a value parameter: `sum[N: u32]: (v: [N]u32): u32`
takes one instantiation per length. The argument is inferred from an owned
array's static length (`sum(a)` with `a: [3]u32` binds `N := 3`) or from a
const-parameterized record's instantiation (`size[T, N: u32]: (r: Ring[T,
N])` recovers both arguments from a `Ring[u8, 8]`), or given explicitly
(`sum[3](a)`). Each instantiation is its own monomorphized function, named
like a record instantiation (`sum_3`); inside the body `N` is an integer
constant of the declared kind, typed by literal-in-context inference. An
explicit argument must be an integer constant within the kind, one const
parameter cannot be bound to two lengths, and a type argument in a const
position is an error. Const parameters carry no resource authority, so
instantiating at two lengths in one scope is ordinary reuse.

A length may be **arithmetic over const parameters**: `[M*K]T`, `[N+1]T`,
with `+ - * / %` and literals. The expression is folded to a literal when
the function is instantiated, so no specialization carries a symbolic
extent — `matmul[M: u32, N: u32, K: u32]: (a: [M*K]f32, b: [K*N]f32):
[M*N]f32` at `matmul[2, 1, 3]` is a function over `[6]f32` and `[3]f32`
returning `[2]f32`, and `out: [M*N]f32` inside its body is a plain owned
array. An arithmetic length binds no parameter by inference (a product does
not determine its factors): each parameter it mentions must be bound from a
plain `[N]T` position or given explicitly, and the folded length is then
checked against the argument like any other type. A fold that is not a
valid length (negative, division by zero, above the `u32` range) rejects
the instantiation.

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

The same totality rule governs the arithmetic operators. `+`, `-`, and `*`
on a fixed-width type wrap mod `2^N` in that width at the expression itself
(so `full + 1` with `full: u8 = 255` is `0` before any store, and
`u16 * u16` never overflows an intermediate `int`); `/` and `%` trap on a
zero divisor and give the two's-complement result for `MIN / -1` (quotient
`MIN`, remainder `0`). Unary minus is total in the operand's own width: `-x` has the type of `x`
for signed and unsigned alike (two's-complement negation mod `2^N`, so
`-MIN` is `MIN` and `-x` for `x: u8 = 1` is `255`); moving between
signednesses stays explicit through `bits`. Ordering and equality on machine
integers follow the same operand rule as arithmetic: one signedness, with
widths promoting, and mixed signedness rejected. The C lowering realizes all
of this with width-specific helpers (unsigned computation, union punning for
signed results), never with C's promoted operators, whose signed overflow
would be undefined.

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

Constraint-carrying generics (`fn [T: Position] sum_xy(p: T)`,
constraints being record shapes, interfaces, or intersections) take the
same road with one addition: **the contract is checked at the
declaration** — the body is validated once against the constraint, so
reading a field the constraint does not grant is an error even if every
caller happens to provide it — and **every call checks its argument**
against the constraint (`OAK-T0104`, naming the inferred binding and the
missing requirement). A call that satisfies the contract specializes the
body exactly as an unconstrained call does, and the specialization is
checked again with the concrete type before emission. Constrained and
unconstrained templates are one mechanism with one emission path.

### 11.3 Floating-point types

**Status: §11.3.1–§11.3.5 and §11.3.8 implemented and tested, including the
`f16`/`bf16` storage formats and hexadecimal literals; float SIMD (§11.3.7),
the `math` library (§11.3.6), and the Lean model are recorded gaps**
(`STATUS.md` lists the implemented subset precisely). This section is
normative for the whole floating-point design. It was motivated by the ml
project's tensor-compiler pilot (`docs/notes/ml-feedback-2026-09.md`,
tier 2), whose numeric core cannot move into Oak without it.

#### 11.3.1 Types

| Type | IEEE 754 format | Role |
| --- | --- | --- |
| `f32` | binary32 | arithmetic type |
| `f64` | binary64 | arithmetic type |
| `f16` | binary16 | **storage** type |
| `bf16` | bfloat16 (8 exponent bits, 7 fraction bits) | **storage** type |

`f32` and `f64` support arithmetic, comparison, conversion, and the
intrinsics of §11.3.5. `f16` and `bf16` support exactly four operations:
load, store, widening to `f32` (`f32(x: f16)`, `f32(x: bf16)`, exact), and
narrowing from `f32` (`f16_round_f32`, `bf16_round_f32`, round to nearest
even). They have no arithmetic, no comparison, and no literals. This is the
surface that half-precision device buffers and quantized inference need,
and it keeps the arithmetic surface at two types.

Floating-point types are machine types in the sense of this chapter: they
are distinct from every integer type and from each other, they participate
in records, arrays, views, spans, ADT payloads, and generic instantiation
like any other scalar, and their layout is the IEEE interchange width
(2, 4, or 8 bytes) with natural alignment.

#### 11.3.2 Literals

A floating-point literal has a fraction, an exponent, or both:

```text
1.5    2.0e-5    1e3    0x1.8p1    0x1p-126
```

Decimal literals are converted to the target format by correct rounding
(round to nearest, ties to even) from the exact decimal value; hexadecimal
literals (`0x` mantissa with `p` binary exponent, C99 §6.4.4.2) are exact
when representable and otherwise correctly rounded; a hexadecimal literal
needs its `p` exponent, since a bare `0x1.8` would be ambiguous with
member access. A literal never has a sign of its own; `-1.5` is unary minus
applied to `1.5`.

Like integer literals (`25-type-inference.md` §3a), a floating-point literal
has no type of its own and takes the floating-point type its context
requires: `x: f32 = 1.5`, `y = 2.0e-5` for `y: f64`, `scale * 0.5` for
`scale: f32`. A floating-point literal in an integer context, or an integer
literal in a floating-point context, is an error at the literal: `x: f32 = 1`
is rejected and spelled `1.0`. A literal with no context at all is `f64`.
A literal that overflows its target format (`x: f32 = 1e39`) is rejected;
one that underflows rounds to a subnormal or zero by the same rule as any
other value.

#### 11.3.3 Semantics fixed in the specification

Floating-point behavior is part of Oak's semantics, not of the backend's
optimization level. The following hold in every backend, every profile, and
the interpreter:

- **Rounding.** Every arithmetic operation and conversion rounds to nearest,
  ties to even. There is no way to change the rounding mode.
- **Subnormals.** Subnormal values are produced and consumed exactly; no
  flush-to-zero, no denormals-are-zero.
- **No rewriting.** A backend may not reassociate, distribute, commute
  across a rounding, or contract floating-point operations. `a * b + c` is
  two roundings; the single-rounding form is spelled `fma(a, b, c)`.
  `x / y` is never rewritten as `x * (1 / y)`; `x - x` is not `0`; `x * 0` is
  not `0`; `x + 0.0` is not `x` (the sign of zero differs). This extends the
  no-hidden-work rule of `90-backend.md` §3 to numeric semantics: the
  written expression is the executed expression.
- **Grouping and evaluation order are semantics.** IEEE addition and
  multiplication are commutative but not associative and not distributive,
  so *which* operations are performed, in *which* grouping, is part of a
  program's meaning. The grouping of a floating-point expression is exactly
  its parse tree: the arithmetic operators are left-associative
  (`a + b + c` is `(a + b) + c`), parentheses group, and no phase may
  regroup. Operands evaluate left to right. Every operation rounds its
  result to its own type before the next operation consumes it — there is
  no excess intermediate precision, so an `f32` expression is computed in
  binary32 at every step even on a target whose registers are wider. Any
  operation over a sequence (a reduction, a dot product, a sum in a library)
  states the order in which it combines its elements, and that order is its
  contract (`55-parallelism.md` §4); `simd.reduce_add` in §11.3.7 is the
  first such statement. Commutativity may be relied on for values;
  `a + b` and `b + a` differ at most in the payload of a NaN result, which
  is unspecified anyway.
- **Comparison.** `<`, `<=`, `>`, `>=` are false when either operand is NaN.
  `==` is false and `!=` is true when either operand is NaN, so `x == x` is
  the portable NaN test in expression form; `is_nan(x)` names it.
  `+0.0 == -0.0` is true. Because `==` is not an equivalence relation on
  floats, `derive.equal`, `derive.hash`, and `derive.compare`
  (`83-modules.md` §6.6) are **not derivable** over a type containing a
  floating-point field; the program writes the ordering it means
  (`total_order(x, y)` below is the IEEE 754-2019 `totalOrder`).
- **Exceptional results.** Division by zero, overflow, invalid operations,
  and inexact results yield the IEEE default result — an infinity, a NaN, or
  a rounded value. They never trap. Oak has no floating-point exception
  flags; a program that needs to detect these conditions tests the result
  (`is_finite`, `is_nan`).
- **NaN payloads.** A NaN produced by an operation is a quiet NaN; the
  payload and sign of an operation's NaN result are unspecified. Programs
  observing NaN payloads through `f32_bits_u32` see *some* quiet NaN.
  Everything else about the bit pattern of every non-NaN result is
  determined.

Consequently, two Oak programs computing the same sequence of operations of
§11.3.5 produce bit-identical results on every conforming implementation.
Only the transcendental library of §11.3.6 is allowed to differ, and it says
by how much.

**Reproducibility is tested, not assumed.** The witness for the rules above
is a differential fuzz (`compiler/differential_float_test.go`): random `f32`
and `f64` expression trees over every grouping of `+ - * /`, unary minus,
and the intrinsics of §11.3.5, with leaves drawn from the IEEE special
values (signed zeros, infinities, NaN, subnormals, the largest finite value,
the 2^53 boundary, non-representable decimals), must agree bit for bit
between an independent reference, the compiled C program, and the
interpreter — on every host the continuous integration runs, which spans
two architectures and two C compilers. A NaN result compares as a class,
since its payload is unspecified. Any proposed backend, optimization, or
host must pass this witness before it is called conforming.

#### 11.3.4 Conversions

Widening between floating-point types is implicit and exact:
`f64(x: f32)`, `f32(x: f16)`, `f32(x: bf16)`. Every other move is an
explicit named conversion in the `{target}_{op}_{source}` scheme of §11.1;
every operation is total:

| Op | Pairs | Semantics |
| --- | --- | --- |
| `round` | `f32_round_f64`, `f16_round_f32`, `bf16_round_f32`; `fN_round_iM` for every integer type `iM`/`uM` | round to nearest even; integers not exactly representable round like any other value (`f32_round_i32(16777217)` is `16777216.0`) |
| `bits` | `f32_bits_u32`, `u32_bits_f32`, `f64_bits_u64`, `u64_bits_f64`, `f16_bits_u16`, `u16_bits_f16`, `bf16_bits_u16`, `u16_bits_bf16` | bit-pattern reinterpretation, total in both directions; every bit pattern is a valid float |
| `trunc` | `iM_trunc_fN`, `uM_trunc_fN` | toward zero; **traps** when the truncated value is outside the target range or the source is NaN |
| `saturating` | `iM_saturating_fN`, `uM_saturating_fN` | toward zero, clamped to the target range; NaN yields `0` |
| `checked` | `iM_checked_fN`, `uM_checked_fN` | `Result[target, Overflow]`; `Err(Overflow)` for out of range and for NaN |

The integer constructor form `f32(x: i32)` is **not** provided, because it
would be exact for some widths and rounding for others; the program spells
the rounding (`f32_round_i32`). `f64_round_i32` and `f64_round_u32` happen
to be exact for every input and are still spelled `round`, so the reader
never has to know which pairs are lossless.

`f32 ↔ c.Float` and `f64 ↔ c.Double` are the bit-preserving constructor
rows already in `92-ffi.md` §2.2 and become implementable with this section.
`f16` and `bf16` have no `c` counterpart; they cross the boundary as
`u16` bit patterns.

#### 11.3.5 Intrinsics under the three-witness rule

The intrinsics below are **correctly rounded**: the result is the exact
mathematical result rounded once by §11.3.3. Only correctly rounded
operations can satisfy Oak's three-witness rule (`92-ffi.md` §3.1) — the
interpreter, the target lowering, and the portable lowering must agree
bit for bit — so this set is exactly the set that admits three equal
witnesses.

| Operation | Spelling | Notes |
| --- | --- | --- |
| add, sub, mul, div | `+ - * /` | operators; `%` is not defined on floats |
| negate | `-x` | flips the sign bit, including of NaN and zero |
| fused multiply-add | `fma(a, b, c)` | one rounding of `a * b + c` |
| square root | `sqrt(x)` | `sqrt(-0.0)` is `-0.0`; negative input yields NaN |
| absolute value, copy sign | `abs(x)`, `copysign(x, y)` | bit operations; total on NaN |
| integer rounding | `floor(x)`, `ceil(x)`, `trunc(x)`, `round(x)` | `round` is ties away from zero (C `roundf`), `round_even(x)` is ties to even; results are floats |
| minimum, maximum | `min(x, y)`, `max(x, y)` | IEEE 754-2019 `minimum`/`maximum`: a NaN operand yields NaN, and `-0.0` is less than `+0.0`. The 2008 `minNum`/`maxNum` behavior (NaN loses) is spelled `min_num`/`max_num` |
| classification | `is_nan(x)`, `is_finite(x)`, `is_infinite(x)`, `is_normal(x)` | return `Bool`; total |
| total order | `total_order(x, y)` | IEEE 754-2019 `totalOrder` as a `Bool`; the ordering `derive.compare` would otherwise need |

Each intrinsic is generic over `f32` and `f64` and monomorphizes like
§11.2; there are no `f16`/`bf16` forms. `Oak.Float` (Lean, planned with the
implementation) states the correctly-rounded contract for each row and
proves the algebraic laws that do hold — `neg` and `abs` are total bit
operations, `copysign` composes, `min`/`max` are commutative on non-NaN
inputs — and does not attempt to prove anything about a transcendental
value.

#### 11.3.6 Transcendentals: a fourth witness

`exp`, `exp2`, `log`, `log2`, `pow`, `sin`, `cos`, `tan`, `tanh`, and their
relatives are **not** intrinsics. They live in a `math` package of the
standard library, and each function documents an error bound in ulps
(units in the last place) relative to the correctly rounded result. The
bound is part of the function's contract; a bound of 1 ulp is the target
for the v1 library and no function ships without a stated bound.

Their verification rule is the **fourth witness**: the interpreter, target
lowering, and portable lowering are each compared to a correctly rounded
reference (an arbitrary-precision evaluation in the test harness) and must
lie within the documented bound. They are *not* required to agree with each
other bit for bit, because libm implementations legitimately differ in the
last place — the ml project observed one ulp of disagreement between two
`exp2f` implementations linked into one process — and pretending otherwise
would make the three-witness rule unsatisfiable. A program that needs
bit-exact transcendental results across implementations must use one
implementation (the `math` package's own, once it exists) and must not
call through `c.extern` to a system libm for the same function.

#### 11.3.7 Floating-point SIMD

`93-simd.md` reserves `simd.F32x4` and `simd.F64x2`. With this section they
acquire the operations `add sub mul div fma min max sqrt neg abs` (lane-wise,
each lane obeying §11.3.3 and §11.3.5), `splat`, `load`, `store`,
`extract_E(v, lane)`, `insert_E(v, lane, x)`, and the horizontal reduction
`simd.reduce_add_E`. Because floating-point addition is not associative, the
reduction's grouping is its semantics (`55-parallelism.md` §4, last option):
`reduce_add_f32x4(v)` is `(v[0] + v[1]) + (v[2] + v[3])` and
`reduce_add_f64x2(v)` is `v[0] + v[1]`, each `+` rounded by §11.3.3. A
backend that has a horizontal-add instruction may use it only if the
instruction produces exactly this grouping. Loads and stores trap on
out-of-range offsets like the integer vectors.

#### 11.3.8 Lowering and interpretation

- **C backend.** `f32` lowers to `float` and `f64` to `double`; `f16` and
  `bf16` lower to `uint16_t` storage with conversion helpers. Every emitted
  translation unit begins with `#pragma STDC FP_CONTRACT OFF`, and the
  `oak run`/`oak test` drivers pass `-ffp-contract=off` (and never
  `-ffast-math`, `-Ofast`, `-ffinite-math-only`, or `-fno-signed-zeros`) to
  the system compiler, so §11.3.3 holds through the C compiler as well.
  Intrinsics lower to the C99 `<math.h>` functions that C99 §F.9 requires to
  be correctly rounded or that are single instructions on every supported
  target (`sqrtf`, `fmaf`, `fabsf`, `copysignf`, `floorf`, `ceilf`,
  `truncf`, `roundf`, `rintf`); `min`/`max` lower to a branch-free helper
  with the 2019 NaN semantics, because `fminf`/`fmaxf` implement the 2008
  ones. Trapping `trunc` conversions lower to a range-checked helper, never
  to C's undefined out-of-range cast.
- **Interpreter.** Go's `float32`/`float64` arithmetic is correctly rounded
  for the operator set and `math.Sqrt`, `math.FMA`, `math.Floor`, `math.Ceil`,
  `math.Trunc`, `math.Round`, `math.RoundToEven`, `math.Copysign`, and
  `math.Abs` are exact or correctly rounded, so the interpreter is a valid
  first witness for every row of §11.3.5. `f32` intrinsics are evaluated in
  `float32` (not via `float64` with a final narrowing, which double-rounds);
  `fma` on `f32` uses the exact `math.FMA` on widened operands, which is
  correct because a binary64 product of two binary32 values is exact.
- **Assembler.** The typed assembler (`94-assembler.md`) does not gain
  floating-point registers in this increment.

#### 11.3.9 What this section does not decide

Declared numeric modes that permit reassociation (`55-parallelism.md` §4,
third option), floating-point atomics, a decimal type, and `f128` are not
part of v1. Each is a separate proposal; none may weaken §11.3.3 for
programs that do not opt in.

## 12. Formal obligations

The executable type lattice must satisfy the laws in §3.

Record/struct verification is split deliberately:

- semantic record proofs cover member uniqueness, shape satisfaction and composition;
- struct representation proofs cover ordered placement, alignment, padding, non-overlap and final size;
- a representation refinement must prove that a concrete `struct` declaration is lowered according to its selected representation policy.

The initial Lean type-lattice model proves its laws over semantic type denotations. Go property/unit tests must exercise the implementation against the same laws.

An implementation is not called refined until we explicitly relate concrete compiler structures/operations to the formal denotation and representation models.
