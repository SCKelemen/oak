# Executable Lowering and Backends

Oak's semantics are not defined by C, but the C backend is an important executable projection and cost-model oracle.

## 1. Backend-independent semantics

The typed/Semantic IR defines program meaning before a backend chooses concrete machine representation.

A backend must preserve:

- value semantics;
- control-flow semantics;
- ownership/effect constraints;
- integer behavior;
- ADT constructor distinctions;
- pattern-match selection;
- required layout/ABI constraints;
- safe bounds and pointer rules.

A backend may optimize representation only when those observations remain equivalent.

## 2. C as bootstrap/reference backend

Generated C should be intentionally straightforward and debuggable.

For systems code, a competent C programmer should recognize the expected machine shape:

```text
semantic record constraint -> erased after specialization; no runtime object required
natural struct             -> C struct / ordered fields
closed ADT                 -> tag + payload or proved equivalent compact representation
match                      -> switch/if branches
specialized fn             -> direct C function / inlineable code
view/span                  -> pointer + length representation
raw pointer                -> C pointer
fixed array                -> fixed storage
arena/slab                 -> explicit allocator calls/storage
```

C is not Oak's semantic definition and should not prevent future native/LLVM/etc. backends.

## 3. No hidden runtime

The backend may not silently introduce:

- heap allocation;
- garbage collection;
- reference counting;
- exception unwinding;
- interface vtables for static generic constraints;
- boxing to a dynamic object representation;
- hidden string/data copying;
- unbounded callback dispatch.

If a selected language feature requires such machinery, the semantic model must expose the corresponding representation/effect.

A semantic record/shape constraint specifically does not authorize the backend to invent a runtime dictionary, boxed record, or vtable. Specialization must resolve its required members against the concrete type.

## 4. Generics

Generic functions/types specialize by default.

Monomorphization should erase compile-time constraints and phantom parameters that have no runtime representation.

Specialization must preserve type/effect semantics and must not introduce dynamic dispatch merely for compiler convenience.

A future explicitly selected code-size/dynamic-dispatch strategy may exist, but it is a distinct representation choice.

## 5. ADTs

The ordinary representation is conceptually:

```text
tag + payload storage
```

A backend can select tag width from the number/representation constraints of constructors.

Payload defaults/metadata are not automatically discriminant values.

A compact enum-like representation is valid only when constructor payload semantics allow it and the representation mapping is injective over observable constructor values.

## 6. Records and structs

A **record** is semantic product/shape information. It may be consumed entirely at compile time and therefore may have no runtime representation at all.

A **struct** selects a concrete product representation policy. Plain `struct` selects Oak's natural ordered policy; target primitive representations must still be known before numeric field offsets and total size are resolved.

The compiler therefore treats these states distinctly:

```text
semantic shape only
representation policy selected
representation resolved
```

The backend may lower only from a representation state sufficient for the operation it is performing. It must fail closed rather than fabricate offsets or sizes.

Target layout computes sizes, alignment, padding and offsets from ordered struct fields plus explicit representation constraints. The backend must not derive representation field order from unordered maps.

FFI/wire/persisted layouts require explicit stable representation contracts rather than relying on incidental target ABI layout.

A shape constraint may be satisfied by concrete types with different layouts because shape satisfaction is about semantic members, not offsets. Specialization resolves field accesses against each concrete representation.

## 7. Integer semantics

Backend operations must implement Oak's specified fixed-width behavior exactly.

C undefined/implementation-defined behavior must not leak into safe Oak semantics. Code generation may need unsigned operations, explicit casts, intrinsics, checks, or helper routines to preserve Oak's rules.

The formal specification of overflow/division/shifts/conversions must precede relying on them for verification.

### 7a. Floating-point semantics

The same rule governs floating point (`20-types.md` §11.3): the backend realizes IEEE 754 round-to-nearest-even with subnormals, never reassociates, distributes, or contracts, and never enables a fast-math mode. The C backend emits `#pragma STDC FP_CONTRACT OFF` at the top of every translation unit that uses floating point (under clang, which honors the standard pragma; gcc does not implement it and never contracts in strict ISO mode, which the drivers select with `-std=c99`/`-std=c11`), spells `f32`/`f64` as `float`/`double`, emits literals as exact hexadecimal floating constants of the checked width so the C compiler performs no decimal conversion of its own, keeps `+ - * /` and comparisons as the plain C operators with every operation parenthesized so C's grouping is Oak's parse tree (`20-types.md` §11.3.3), requires `FLT_EVAL_METHOD == 0` of the target (the emitted unit fails to compile on a target that evaluates in excess precision, such as x87, rather than silently changing results), and lowers intrinsics to the correctly rounded C99 `<math.h>` functions (with its own helpers for the IEEE 754-2019 `min`/`max` and `totalOrder`). The `oak run`/`oak test` drivers pass `-ffp-contract=off` and link `-lm`; `-ffast-math`, `-Ofast`, `-ffinite-math-only`, and `-fno-signed-zeros` are never passed. Out-of-range float-to-integer conversions lower to range-checked helpers that trap, saturate, or report, never to C's undefined cast. The "no hidden runtime" rule of §3 extends to numeric semantics: the written expression is the executed expression.

## 8. Bounds

When the compiler proves an index/range safe, a backend may eliminate the corresponding dynamic check.

When safety is not proved, safe Oak must retain a defined check/failure path rather than compile to out-of-bounds undefined behavior.

## 9. Function values/closures

A plain function value may lower to a function pointer.

A capturing closure requires an explicit environment representation whose storage lifetime has been established by ownership/effect analysis.

The backend may not silently heap-promote escaping captures.

## 10. Source/debug information

Backend output should preserve mappings from generated operations to canonical Oak source spans and stable semantic identities.

The compiler's source model should power:

- C `#line` / debug mappings where useful;
- DWARF/native debug metadata in future backends;
- diagnostics and IDE navigation;
- semantic debugger schemas.

## 11. Verification strategy

Backend verification proceeds in layers:

```text
semantic operation
  -> representation selection
  -> representation resolution
  -> lowering rule
  -> backend representation/code
  -> executable equivalence/property test
  -> formal refinement for critical rules
```

Early formal-refinement candidates:

- fixed-width integer lowering;
- natural struct layout calculation;
- semantic record-shape satisfaction;
- ADT tag/payload lowering;
- match lowering;
- view/span representation and bounds;
- erased phantom/proof parameters;
- effect-free generic specialization.

The C backend should maintain golden/compile/run tests in addition to formal models. Formal models do not replace generated-code testing.

## C identifier mangling

An Oak value or field identifier is emitted verbatim into C unless its
spelling is a C keyword (`short`, `signed`, `default`, `register`, …), a
leading-underscore name (reserved to the C implementation), or a name in
the emitter's own `oak_` namespace (`oak_assert`); those emit as
`oak_id_<name>` at every site — locals, parameters, globals, record field
declarators and accesses, designated initializers, `offsetof` operands,
match binders. Function names are not routed through this mapping: they
already carry the `oak_` (or package) prefix. The mapping is one function
(`codegen/identifiers.go`, `cIdent`) and idempotent, so nested emitters
cannot double-mangle. Oak keywords (`struct`, `type`) cannot be
identifiers at all, and Oak's own type spellings (`int`, `u32`) lower
through the type table, never through this mapping. Compiler temporaries
live in the reserved `__` namespace (`oak__scrutinee_0`, `__oak_tail_0`),
which user identifiers can never spell (`83-modules.md`), so the mapping
passes them through untouched.

## 9. Small helpers

Naming an operation must not cost a call. A private (not `pub`), named,
non-generic, non-method function with an Oak body that calls no user-defined
function, contains no loop, and spans at most twelve source lines is emitted
as a forced-inline helper (`OAK_INLINE`: C99 `extern inline` with the
always-inline attribute) in both its prototype and definition. The C
compiler then inlines every call at every optimization level, including
`-O0`, rather than by heuristic, while the external definition is still
emitted so the symbol remains available to linkers and assembly inspection. Exported, extern, and asm-backed functions
keep external linkage; recursive and looping functions are never marked, so
the C compiler is never asked to inline what it cannot. The judgment is the
discipline analyzer's call-graph and loop walk (`InlineHelperShape`), so the
backend and the recursion policy share one authority.

## 10. Owned arrays as values

An owned array `[N]T` is a value, and its C representation is a struct
carrying the array: `typedef struct oak_arr_T_N { T v[ N ]; } oak_arr_T_N;`
(`codegen/arrays.go`). The wrapper has exactly the raw array's size and
alignment, so record layouts and the emitted `sizeof`/`offsetof` assertions
are unchanged, and C's own struct semantics supply every copy the language
specifies: a parameter is the callee's own copy (no copy-in prologue), a
return is a copy, whole-array assignment and initializing a record field
from an array binding are plain assignments, and a tagged-union payload of
array type is stored and matched like any other. Element access spells
`.v` before the index and keeps its bounds check (`oak_index`, `oak_store`,
`oak_lv_idx` take the array member); `view(&a)` / `span(&a)` borrow `a.v`
with the static length; `a[lo:hi]` over an owned array is a compound-literal
view whose bounds are checked against the static length before the pointer
is formed, so a slice is a value in argument position too. A typed array
literal is a compound literal of the wrapper, `(oak_arr_u32_4){ { 1, 2, 3, 4 } }`,
in any expression position; a declaration initializer is the brace form. The
typedef name mangles element spellings that are not identifiers (`_Atomic u32`,
`void *`, a nested `oak_arr_u8_16`); wrapper typedefs are placed before the
first record, union, global, or prototype that names them, and a type that
first appears inside a function body fails closed with an `OAK_UNSUPPORTED`
marker rather than emitting a typedef where C forbids one.

