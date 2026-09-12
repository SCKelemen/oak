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

These laws, and the soundness and completeness of the normal-form procedure the checker decides them with, are stated in Oak over that procedure and decided by `oak prove` (`spec/oak/lattice.oak`; `125-verification.md` §6.1): a clause is the mask of the atoms it requires, a normal form the bitset of its clauses, and the procedure agrees with the pointwise semantics on every normal form of three atoms and every four-node type. `spec/lean/Oak/TypeLattice.lean` and `TypeLatticeRefinement.lean` prove the same for any number of atoms.

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

A record template's literal takes its type arguments from the expected
type (`Segment { ... }` against `Segment[Fresh]`), or is an error asking for
an annotation; typestate-indexed resource handles (`112-protocols.md` §5a)
are the first use, with the protocol's states as phantom markers.

## 10. Refinements and GADT direction

Refinements add propositions to a base type:

```text
{x : u16 | x < N}
```

A refined type denotes the subset of its base type satisfying the proposition. General value-refinement surface syntax remains future work.

GADT-style constructors extend the same idea to constructor-specific result refinements. Constructor result-index syntax and equality solving are normative in `30-adts-patterns.md`: fixed result indices and repeated result parameters introduce equality propositions. More general propositions must extend this refinement system rather than create a separate object system.

## 11. Machine types

Fixed-width integer types (`u8`..`u64`, `u128`, `i8`..`i64`) have exact machine-width semantics. Target-width integer/pointer-sized types are distinct semantic types whose widths are supplied by the target.

`u128` is the one width above the machine word: an unsigned 128-bit
integer for checksums, identifiers, and the wide halves of a wire header
(the storage engine's frame header; TigerBeetle's `u128` fields, noted in
`docs/notes/tigerbeetle-2026-09.md`). It follows every rule of the other
widths — `+`, `-`, `*` wrap mod `2^128`, `/` and `%` trap on zero, shifts
by a count reaching 128 trap, ordering is unsigned — and has the same
constructor and conversion vocabulary (§11.1): `u128(x)` widens from every
unsigned type and admits every non-negative literal, including those above
`2^63`; `u64_trunc_u128`, `u64_saturating_u128`, and `u64_checked_u128`
(and the narrower unsigned targets) come back down. There is no `i128`, no
`bits` reinterpretation at 128, and the checked arithmetic family (§11.1a)
stops at 64 bits. In the C lowering `u128` is `unsigned __int128`: 16
bytes at 16-byte alignment on every LP64 target Oak emits for, ratified by
the emitted `sizeof`/`_Alignof` assertions (`40-records.md` §6a); a C
compiler without `__SIZEOF_INT128__` leaves the type undefined, so a
program using it fails to build there rather than narrowing. The
interpreter computes every operator exactly and folds into the width; the
Lean extraction has no 128-bit machine integer and reports a `u128`
function as outside its subset (`95-extraction.md`). The `wide` module
(`wide := import("wide")`) provides `wide.pack(upper, lower)`,
`wide.high(x)`, and `wide.low(x)` for the two `u64` halves a frame reads
and writes; it is a module of its own so a program that never names
`u128` — a 32-bit freestanding target whose C compiler has no 128-bit
integer — emits no `u128` declaration.

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
signedness (constructor form: `i32(x: i8)`, `u64(x: u32)`, `u128(x: u64)`;
unsigned also widens into a strictly wider signed type, of which there is
none above `u64`). Every other move between machine
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
would be undefined. The helper bodies are transliterated line for line
and proved equal to the fixed-width operators — the extraction's
semantics — in `spec/lean/Oak/ArithmeticRefinement.lean`, with the emitted
text pinned by `codegen/arithmetic_refinement_test.go`
(`65-machine-memory.md` §12).

### 11.1a Checked, saturating and trapping arithmetic

Wrapping is the operators' contract, not always the program's. Offsets,
lengths, sequence numbers, and epochs must *notice* the wrap, and a guard
written by hand before every `+` is the kind of code that is right in the
common case and wrong at the boundary. The arithmetic family makes the
intent a spelling, in the same `{type}_{op}_{kind}` grammar as the
conversions:

| Function | Result | Semantics |
| --- | --- | --- |
| `{type}_checked_add(a, b)`, `_sub`, `_mul` | `Result[type, Overflow]` | `Ok(exact)` when the mathematical result is in the type's range, `Err(Overflow)` otherwise |
| `{type}_saturating_add(a, b)`, `_sub`, `_mul` | `type` | the exact result clamped to the type's range, on the side it left |
| `{type}_trapping_add(a, b)`, `_sub`, `_mul` | `type` | the exact result when it fits; otherwise the program stops at a located trap (`oak: arithmetic overflow at file:line` in hosted builds, the bare trap freestanding), exactly as a failed `assert` does |

`type` is any fixed-width integer (`u8`..`u64`, `i8`..`i64`); both operands
have that type (untyped literals infer against it) and there is no implicit
widening between operands — the width is stated once, in the name. The
checked forms need the program to declare `Result[T, E]` (Ok/Err) and
`Overflow` like the checked conversions; `import(std)` provides both.
Saturation is defined by the exact result, so `i8_saturating_mul(-128, -1)`
is `127` and `u32_saturating_sub(1, 2)` is `0`. The trapping forms are the
overflow-loud posture for hot paths that would rather stop than branch:
`u64_trapping_add(lsn, 1)` never yields a wrapped log sequence number, and
the trap names the call site. There is no `wrapping` spelling: the operator
is it. A discipline profile that rejects the plain operators on integers
unless a wrapping intent is spelled remains direction — every loop counter
is a `+`, so the rejection needs an opt-in narrower than `strict`
(85-discipline.md) before it is useful. What is implemented is the narrow
report that catches the shape where accidental wrap is a security bug: an
unsigned `+` or `*` computed *inside an ordering comparison* (`off + len <=
cap`, `n * size < limit`) is reported as `OAK-T0701` at information
severity — listed by `oak vet`, rejected by no profile (85-discipline.md
§6a). The report names the carrier and the spelling that states the intent
(`u32_checked_add`, `u32_saturating_add`); subtraction is not reported,
because `off <= cap - len` is the recommended shape and its precondition
(`len <= cap`) is a guard the reader can see.

`spec/lean/Oak/CheckedArithmeticRefinement.lean` transliterates the C helper
bodies over the builtins' contract and proves them to this section — in
particular that each saturating side test picks the bound the exact result
left — with the emitted text pinned by
`codegen/checked_arithmetic_refinement_test.go`.

The interpreter computes the exact result in arbitrary precision and
compares it with the range (a trapping overflow is its error, as a failed
assertion is); the C backend uses the type-generic overflow builtins
(`__builtin_add_overflow` and friends), which report whether the exact
result fits without evaluating a signed overflow in C — the same gcc/clang
baseline the trapping helpers already assume. Both realizations are
exercised at every boundary value of every width by
`compiler/e2e_checked_arithmetic_test.go` and
`compiler/e2e_trapping_arithmetic_test.go` (in range through both, the
overflow trap per program through both), and the differential witness
requires them to agree. Division has no checked form: `/` and `%` already
trap on zero and are total otherwise (`MIN / -1` is `MIN`).

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

**Status: §11.3.1–§11.3.8 implemented and tested, including the `f16`/`bf16`
storage formats, hexadecimal literals, the float vectors, float fields in
records with `size_of`/`align_of`/`offset_of` over float types, and the
complete v1 `math` package (`exp exp2 expm1 log log2 log1p sin cos tan asin
acos atan atan2 sinh cosh tanh asinh acosh atanh pow`). `Oak.Floats`
(`spec/lean/Oak/Floats.lean`) models the evaluation discipline of §11.3.3
— one rounding per operation over an idealised binary format, grouping as
the parse tree, `fma` as a single rounding — and proves that any two
conforming implementations agree on every expression, that rounding is the
identity on representable values (widening is exact), that addition and
multiplication commute, and, by decided witnesses, that reassociation and
contraction change results. Special values, overflow, and subnormals are
outside the model and are executed by the witness tests** (`STATUS.md` lists the implemented subset precisely). This section is
normative for the whole floating-point design. It was motivated by the ml
project's tensor-compiler pilot (`docs/notes/ml-feedback-2026-09.md`,
tier 2), whose numeric core cannot move into Oak without it.

#### 11.3.1 Types

| Type | Format | Role |
| --- | --- | --- |
| `f32` | binary32 | arithmetic type |
| `f64` | binary64 | arithmetic type |
| `f16` | binary16 | **storage** type |
| `bf16` | bfloat16 — the Brain floating-point convention (1 sign, 8 exponent, 7 fraction bits: the upper half of binary32), not an IEEE 754 interchange format; rounding and specials follow binary32 truncated to 16 bits | **storage** type |
| `f8e4m3` | OCP FP8 E4M3 (4 exponent bits, 3 fraction bits, bias 7; no infinities, NaN is `S.1111.111`, largest finite 448) | **storage** type |
| `f8e5m2` | OCP FP8 E5M2 (5 exponent bits, 2 fraction bits, bias 15; infinities and NaN as IEEE, largest finite 57344) | **storage** type |

`f32` and `f64` support arithmetic, comparison, conversion, and the
intrinsics of §11.3.5. The storage types support exactly four operations:
load, store, widening to `f32` (`f32(x: f16)`, `f32(x: bf16)`,
`f32(x: f8e4m3)`, `f32(x: f8e5m2)`, exact), and narrowing from `f32`
(`f16_round_f32`, `bf16_round_f32`, `f8e4m3_round_f32`,
`f8e5m2_round_f32`, round to nearest even). They have no arithmetic, no
comparison, and no literals. This is the surface that half-precision device
buffers and quantized inference need, and it keeps the arithmetic surface
at two types.

The 8-bit formats follow the OCP 8-bit Floating Point Specification (OFP8)
v1.0. Their overflow rules differ, and the `round` row keeps each format's
own: a value beyond 448 in magnitude rounds to the E4M3 NaN (the format
has no infinity to round to; 464, the tie between 448 and the NaN code,
rounds to the even 448), and a value beyond 57344 rounds to the E5M2
infinity. Every NaN narrows to the format's quiet NaN without payload and
widens quiet. Because clamping is the common contract for activations and
weights, the 8-bit formats also have a **saturating** narrowing,
`f8e4m3_saturating_f32` and `f8e5m2_saturating_f32`: finite overflow
clamps to the largest finite magnitude of the same sign, NaN stays NaN,
and an infinity stays an E5M2 infinity. Both narrowings are executed
bit for bit in the compiler's C helpers and in the interpreter, which the
tests sweep against each other over every 8-bit pattern and every `f32`
upper half (`compiler/e2e_f8_storage_test.go`).

Floating-point types are machine types in the sense of this chapter: they
are distinct from every integer type and from each other, they participate
in records, arrays, views, spans, ADT payloads, and generic instantiation
like any other scalar, and their layout is the IEEE interchange width
(1, 2, 4, or 8 bytes) with natural alignment.

#### 11.3.1a Block formats: MXFP4 (`import("mx")`)

Packed 4-bit with block scales is a block format, not a scalar, and it is
a library package rather than a type: `stdlib/mx.oak` implements the OCP
Microscaling (MX) MXFP4 block — thirty-two E2M1 elements (sign, two
exponent bits, one fraction bit; the eight magnitudes 0, 0.5, 1, 1.5, 2,
3, 4, 6) packed two to a byte under one E8M0 scale (an unsigned exponent
with bias 127, `2^-127` through `2^127`; `0xFF` is NaN) — in Oak over the
`f32` and `u32` bit operations, so it runs identically compiled and
interpreted.

| Name | Meaning |
| --- | --- |
| `mx.Fp4Block` | `struct { scale: u8, packed: [16]u8 }`, a proven 17-byte layout; element `i` is in `packed[i / 2]`, even indices in the low nibble |
| `mx.fp4_round_f32(x)` | nearest E2M1 code, ties to even; magnitudes past 6 clamp to 6; NaN is zero; infinities clamp with their sign |
| `mx.fp4_widen(code)` | the element's value as `f32`, exact |
| `mx.e8m0_widen(code)` | the scale's value as `f32`, exact |
| `mx.fp4_scale_of(values)` | the block scale: the largest power of two at or below the largest magnitude, divided by 4 (the largest E2M1 power of two), clamped to the E8M0 range; an all-zero block, or one whose largest magnitude is NaN or infinite, scales by 1 |
| `mx.fp4_quantize(values: [32]f32)` | the block: each value divided by the scale (an exact power of two) and rounded by `fp4_round_f32` |
| `mx.fp4_get(block, i)`, `mx.fp4_dequantize(block)` | the scale times the element, exact except where the product leaves the `f32` range |

The scale rule is OCP MX v1.0 §6.3 for a single block; the tie and clamp
rules are executed against a Go rendering of the same arithmetic over
every element code, every rounding tie, and a sweep of pseudo-random
blocks (`compiler/e2e_mx_test.go`). Element-wise arithmetic on a block is
not provided: a kernel widens to `f32` and computes there.

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
| `round` | `f32_round_f64`, `f16_round_f32`, `bf16_round_f32`, `f8e4m3_round_f32`, `f8e5m2_round_f32`; `fN_round_iM` for every integer type `iM`/`uM` | round to nearest even; integers not exactly representable round like any other value (`f32_round_i32(16777217)` is `16777216.0`); the 8-bit formats overflow by their own rule (§11.3.1) |
| `bits` | `f32_bits_u32`, `u32_bits_f32`, `f64_bits_u64`, `u64_bits_f64`, `f16_bits_u16`, `u16_bits_f16`, `bf16_bits_u16`, `u16_bits_bf16`, `f8e4m3_bits_u8`, `u8_bits_f8e4m3`, `f8e5m2_bits_u8`, `u8_bits_f8e5m2` | bit-pattern reinterpretation, total in both directions; every bit pattern is a valid float |
| `trunc` | `iM_trunc_fN`, `uM_trunc_fN` | toward zero; **traps** when the truncated value is outside the target range or the source is NaN |
| `saturating` | `iM_saturating_fN`, `uM_saturating_fN`; `f8e4m3_saturating_f32`, `f8e5m2_saturating_f32` | toward zero, clamped to the target range; NaN yields `0`. Into the 8-bit formats: nearest even, finite overflow clamped to the largest finite magnitude, NaN kept |
| `checked` | `iM_checked_fN`, `uM_checked_fN` | `Result[target, Overflow]`; `Err(Overflow)` for out of range and for NaN |

The integer constructor form `f32(x: i32)` is **not** provided, because it
would be exact for some widths and rounding for others; the program spells
the rounding (`f32_round_i32`). `f64_round_i32` and `f64_round_u32` happen
to be exact for every input and are still spelled `round`, so the reader
never has to know which pairs are lossless.

`f32 ↔ c.Float` and `f64 ↔ c.Double` are the bit-preserving constructor
rows already in `92-ffi.md` §2.2 and become implementable with this section.
The storage formats have no `c` counterpart; `f16` and `bf16` cross the
boundary as `u16` bit patterns, `f8e4m3` and `f8e5m2` as `u8`.

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

**Implemented** (`stdlib/math.oak`, `import("math")`): `exp`, `exp2`,
`expm1`, `log`, `log2`, `log1p`, `sin`, `cos`, `tan`, `asin`, `acos`,
`atan`, `atan2`, `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`, and
`pow` over `f64` and their `_f32` forms, written in Oak itself — the fdlibm
algorithms over the correctly rounded primitives of §11.3.5, with
Cody–Waite split constants spelled as hexadecimal literals. The
trigonometric functions reduce by fdlibm's three-round Cody–Waite
subtraction for |x| < 2^20 π/2 and by a Payne–Hanek reduction beyond it:
the 53-bit significand of x times the 32-bit limbs of 2/π that matter,
exact in integer arithmetic, modulo 4, with the 192-bit remainder converted
to a double-double before the kernels; `sin(1e22)`, the largest finite
`f64`, and Kahan's hardest argument (6381956970095103 · 2^797) are all
within the bound. Because every operation they use is bit-exact across
implementations, the interpreter and every backend produce **identical
bits**; this is the bit-exact implementation the last paragraph of this
section asks for, and the one a program that reproduces training runs
should use. Documented bounds: 1 ulp for `exp exp2 expm1 log log2 log1p sin
cos tan asin acos atan pow`; 2 ulp for `atan2` (atan's error plus the π
correction, observed near 1 ulp), for `tanh` (it composes `expm1` with a
division; the witness observes up to about 1.5 ulp), and for `sinh cosh
asinh acosh atanh`, which are compositions of `exp`, `expm1`, `log`,
`log1p`, and `sqrt` (observed up to about 1.4 ulp). `atan2` follows C99
Annex F.9.1.4 for its special values (signed zeros, ±π, ±π/2, and ±π/4 or
±3π/4 for two infinities). `pow` follows IEEE 754-2019 and C99
Annex F.9.4.4 for its special values — x^0 and 1^y are 1 even for NaN,
signed zeros and infinities follow the parity of an integer exponent, a
negative base with a non-integer exponent is NaN — and representable
integer powers are exact. The `_f32` forms compute at `f64` and round once
and are within 0.5 ulp on the witness corpus. This completes the v1
library; a correctly rounded (0.5 ulp) tier would be a separate design.

Their verification rule is the **fourth witness**: the interpreter, target
lowering, and portable lowering are each compared to a correctly rounded
reference (an arbitrary-precision evaluation in the test harness) and must
lie within the documented bound. They are *not* required to agree with each
other bit for bit, because libm implementations legitimately differ in the
last place — the ml project observed one ulp of disagreement between two
`exp2f` implementations linked into one process — and pretending otherwise
would make the three-witness rule unsatisfiable. A program that needs
bit-exact transcendental results across implementations must use one
implementation (the `math` package's own) and must not call through
`c.extern` to a system libm for the same function. The witness is
`compiler/e2e_math_test.go`: an arbitrary-precision reference (`math/big`,
320 bits) over a corpus of special points and random arguments per
function and width; it reports the worst observed error per function and
fails on any case beyond the documented bound, and it additionally
requires the compiled and interpreted results to be bit-identical, which
the Oak-source implementation guarantees. The trigonometric corpus includes
the `f64` nearest to k π/2 for random k (arguments whose true remainder is
far below their own ulp), arguments up to the largest finite `f64`, and
Kahan's hardest reduction case; the `pow` corpus covers every Annex F
special case, both signs of base with integer and non-integer exponents,
and results at the overflow and subnormal boundaries; the inverse
functions are checked at each of their interval boundaries (7/16, 11/16,
19/16, 39/16 for `atan`; 0.5 and 0.975 for `asin`; 2^-26, 2, 2^26 for the
hyperbolic inverses) and at arguments within 10^-15 of ±1.

#### 11.3.7 Floating-point SIMD

`93-simd.md` §1.2a defines `simd.F32x4` and `simd.F64x2` (implemented). With
this section they carry the operations `add sub mul div fma min max sqrt neg abs` (lane-wise,
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
  `bf16` lower to `uint16_t` storage and `f8e4m3` and `f8e5m2` to
  `uint8_t`, each with conversion helpers. Every emitted
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

## 12. Refinement types

```oak
Slot: type = u16 where value < u16(8)
Even: type = u8 where value % u8(2) == u8(0)
```

`Name: type = Base where pred` declares a nominal type whose values are the
values of `Base` — a machine integer type — that satisfy `pred`, a `Bool`
expression over `value`, the candidate, checked like any expression with
`value` bound at the base (`OAK-T0602` for a base that is not an integer
type or a predicate that is not `Bool`). `where` is contextual.

A refined value flows to its base freely: assigning it to a `u16`, passing
it to a `u16` parameter, and arithmetic on it all drop the refinement, as
arithmetic drops any nominal distinction. A base value becomes refined only
through the checked construction `Name(v)`: the value is returned if `pred`
holds and the program traps otherwise, the same trap as a failed
`assert`. Nothing else produces a refined value, so a binding of a refined
type carries `pred` as a fact wherever it is in scope.

That fact is the point (`50-borrowing.md`, extent facts): a parameter or a
binding of a refined type contributes `pred` with `value` read as the
binding to the extent facts, so `TABLE[i]` with `i: Slot` and an
eight-element `TABLE` is proven and emitted unchecked. The bounds check
moved from every access to the one construction, where it can often be
folded away (a literal argument) or discharged by a theorem
(`125-verification.md`).

Representation: the base's. The backend emits `typedef` of the base and one
guard function per refinement (`oak_refine_Name`); the interpreter binds the
name to the assertion; the prover enumerates a refined parameter as the
base values the construction accepts. The Lean extraction types a
refinement as its base, states a construction as the value guarded by its
predicate (`none`, the trap, otherwise), and gives a theorem over a
refined parameter the predicate as a hypothesis (`125-verification.md`
§5).

Static discharge: when the facts in scope prove the predicate of the
argument, the construction is emitted as a plain conversion with no guard.
The predicate is read by shape, and each shape is discharged by a law the
extent facts already carry (`50-borrowing.md`, `Oak.Extents`) or by
evaluation:

- `value < K`, `value <= K` with a literal `K`: the argument is proven
  below the bound by the index laws — a loop counter under its guard, a
  masked value, a literal, a value already refined by a tighter type;
- `value >= K`, `value > K`: a literal lower bound on the binding in scope
  (a guard `k >= 1`, a refined parameter), or a constant;
- `value % K == 0` with `K` a power of two: the argument's low bits are
  zero by its shape — `p << 12`, `a & ~4095`, `x * 2`, a sum, difference,
  or bitwise combination of such terms, a conversion of one. Wrapping
  arithmetic keeps a power-of-two divisor's low bits, which is why `K`
  must be one;
- `a && b`: both parts; `a || b`: either;
- a constant argument: the predicate is evaluated at the base width, with
  the base's wrapping arithmetic (`Even(u8(4))` costs nothing, `Even(u8(7))`
  keeps its guard and traps);
- an argument already of a refinement with the same predicate
  (`Even(e)` with `e: Even`).

Conversely an index that is a construction `Name(e)` is proven below the
predicate's upper bound — the tightest `value < K` conjunct — whether or
not the guard was discharged: the guard trapped otherwise. So
`TABLE[Slot(i)]` under `i < 8` costs nothing at all, and `TABLE[Slot(n)]`
for an arbitrary `n` costs the one guard. Anything the shapes do not cover
keeps its guard: a check that stays is a runtime check, never a silent
assumption.

A refined return type is a postcondition: `low: (x: u16): Slot =
Slot(x & u16(7))` must construct (returning the bare `u16` is refused), and
a caller may index through the call directly — `TABLE[low(x)]` is proven,
because any expression of a refined type is below the bound.

A binding declared without an initializer (`state: Sha256State`) is
zero-initialized, so it is admitted only when zero satisfies every
refinement its type holds, field by field (`OAK-T0602` otherwise: `the
zero value of Rec.p is outside the refinement Pos; initialize it`) —
nothing else produces a refined value. A record field of a refinement
type has its base's representation, and a store through a refined index
is proven like a read — the shape of a hash state whose fill field is a
`value < 64` refinement: every byte stored into the block is proven, and
the construction that advances the fill is discharged by the arm it sits
in (`fill < 63 ? { fill = Fill(fill + 1) } | { compress; fill = Fill(0) }`).

`oak vet` reports the count of constructions discharged statically and
guarded at run time, so the checks a program still pays are never hidden.

### 12.1 Generic refinements

```oak
IrqId[N: u32]: type = u16 where value < N

route: (table: [4]Handler, i: IrqId[4]): Handler = table[i]
```

A refinement whose type parameters are integer constants (§11, const
parameters) is a template over the predicate. Each application `IrqId[4]`
— in a parameter or binding type, in a field type, in a construction
`IrqId[4](v)` — is a distinct nominal refinement whose predicate has the
literal substituted (`value < 4`), so `IrqId[4]` and `IrqId[8]` are not
assignable to each other and each carries its own bound as a fact:
`table[i]` above is proven, and `table[IrqId[4](k)]` under `k < 4` is
discharged at the construction too. Applications are specialized before
checking, into declarations named like record instantiations (`IrqId_4`),
and every later phase — the extent facts, the backends' guards, the Lean
projection, the interpreter, the prover — sees only those. Arguments are
integer literals within the parameter's kind (`IrqId[300]` with `N: u8` is
an error, `OAK-T0602`); an application with the wrong count of arguments
or a parameter that is a type rather than a constant is refused the same
way. An application whose argument is the const parameter of an enclosing
template — a record template's field `slot: IrqId[N]`, a generic
function's `make[N: u32]: (v: u16): IrqId[N] = IrqId[N](v)` — is
specialized when the enclosing template is instantiated, so `Table[8]`
holds an `IrqId_8` and `make[8]` constructs one; `[4]IrqId[N]` is an
array of the application. A record field of a refinement type has its
base's representation in the backend.

Not yet: refinements over records and floats, and the discharge of a
construction from a declared theorem rather than the facts in scope. Each
stays a runtime check until then, never a silent one.

