# Foreign Interfaces: the `c` Library and Abstract Assembly

Oak's verified core ends where the machine begins. This chapter specifies the
two doors through that boundary — the C interface and the assembly interface —
and the rule that governs both: **crossing the boundary looks like an ordinary
typed function call, and every assumption the call imports is written down.**

## 1. Design position

- Foreign code is reached through **clean function abstractions**, never
  through inline foreign syntax embedded in Oak bodies. There is no inline C
  and no inline assembly in expression position.
- The C ABI surface lives in one special library named `c`. Its members
  (`c.Int32`, `c.String`, `c.Ptr`, …) are the only types an extern signature
  may mention, so a foreign signature is honest about being foreign.
- Assembly is exposed the way Go exposes it: an **abstract machine interface**
  with per-architecture instruction functions (`arm64.*` today), lowered by
  each backend to the real instruction where the target has it and to a
  proven-equivalent portable sequence where it does not. Programs written
  against the interface are total and portable; the instruction is a
  performance guarantee, not a semantics change.

## 2. The `c` library

`c` is a compiler-known library, not a user package. It cannot be reassigned
or extended from Oak source. In **type position** the name always resolves to
the library (`x: c.Int32` is never a local). In **expression position** an
ordinary local binding named `c` shadows the library — `c` stays a usable
variable name — and the library interpretation applies only where no such
binding is in scope. The same rules govern the architecture libraries
(`arm64`).

### 2.1 Types

| Oak spelling | C spelling | Notes |
| --- | --- | --- |
| `c.Char` | `char` | signedness is implementation-defined in C |
| `c.Int8` / `c.UInt8` | `int8_t` / `uint8_t` | |
| `c.Int16` / `c.UInt16` | `int16_t` / `uint16_t` | |
| `c.Int32` / `c.UInt32` | `int32_t` / `uint32_t` | |
| `c.Int64` / `c.UInt64` | `int64_t` / `uint64_t` | |
| `c.Int` / `c.UInt` | `int` / `unsigned int` | width per §2.4 target model |
| `c.Long` / `c.ULong` | `long` / `unsigned long` | width per §2.4 target model |
| `c.Size` | `size_t` | |
| `c.Float` / `c.Double` | `float` / `double` | |
| `c.Bool` | `_Bool` | |
| `c.Ptr` | `void *` | opaque; not dereferenceable in Oak |
| `c.String` | `const char *` | NUL-terminated; length is **not** carried |

Every `c.*` type is **nominal** and distinct from every Oak type. There is no
implicit conversion in either direction, no arithmetic, and no ordering on
`c.*` values in v1: they exist to be constructed, passed across the boundary,
and converted back. `c.Ptr` and `c.String` cannot be dereferenced, indexed, or
stored through from Oak — the borrow checker never sees a foreign pointer as
an owner.

### 2.2 Conversions

Conversions are explicit constructor calls, exactly like Oak's numeric casts,
and are defined only for the pairs below (both directions):

| Oak type | c type | Law |
| --- | --- | --- |
| `i8`…`i64`, `u8`…`u64` | same-width, same-signedness `c.IntN`/`c.UIntN` | value-preserving bijection |
| `u8` | `c.Char` | byte reinterpretation |
| `i32` / `u32` | `c.Int` / `c.UInt` | valid under the §2.4 target model |
| `u32` | `c.Size` | widening injection (`size_t` ≥ 32 bits under §2.4) |
| `f32` / `f64` | `c.Float` / `c.Double` | bit-preserving |

```oak
n: c.Int = c.Int(code)      // code: i32
back: i32 = i32(n)
```

The fixed-width rows are total bijections in both directions;
`Oak.CInterop` (Lean) proves the mapping is injective and round-trips.
`c.Size(x: u32)` is injective but its inverse is a checked narrowing, which is
not provided in v1 — keep lengths in `u32` on the Oak side.

### 2.3 Extern bindings

An extern binding is an ordinary declaration-form function whose definition is
`c.extern("symbol")`:

```oak
putchar: (ch: c.Int): c.Int = c.extern("putchar")
abort: (): () = c.extern("abort")
```

Rules (diagnostics `OAK-F01xx`):

- **F0101** — every parameter type and any non-unit return type of an extern
  binding must be a `c.*` type. Oak types never cross the boundary raw.
- **F0102** — the symbol must be a single string literal that is a valid C
  identifier (`[A-Za-z_][A-Za-z0-9_]*`). This is load-bearing for the C
  backend: the symbol is emitted into generated source, and the identifier
  grammar is what makes that emission injection-free.
- **F0103** — `c.extern` is only a definition; it cannot appear as an
  expression anywhere else.
- Extern bindings take no variadic parameter, no generic parameters, and no
  receiver in v1.

Calling an extern binding is ordinary safe Oak. **The declaration is the
trust boundary**: by writing the binding, the author asserts the foreign
symbol exists with exactly the declared ABI signature and honors it. This
assumption is *not* checked by Oak and is recorded here as the FFI trust rule
(the analogue of an `unsafe` block's obligation, hoisted to the one
declaration site instead of every call site). Discipline profiles may later
require an audit manifest of extern bindings; the strict profile does not yet.

The C backend emits its own `extern` prototype derived from the binding — it
does not include foreign headers. A mismatch between the binding and the true
symbol is a foreign-contract violation, exactly like a wrong prototype in C.

### 2.4 Target model (recorded assumption)

v1 code generation assumes an ILP32 or LP64 C target: `int` is exactly 32
bits, `size_t` is at least 32 bits. Targets outside this model (16-bit `int`)
are not supported by the v1 `c.Int`/`c.Size` conversion rows; the fixed-width
rows are unconditional.

### 2.5 Spans at the boundary

**Status: implemented and tested** for fixed-width integer and `Bool`
elements (`STATUS.md`; the implemented subset is stated in §2.5.4).
Motivated by the ml project's pilot, where every byte of kernel source left
the process through one `putchar` call because no buffer could cross the
boundary (`docs/notes/ml-feedback-2026-09.md`, tier 3).

§2.1 makes `c.Ptr` and `c.String` opaque and constructor-less, which is the
right rule for pointers that come *from* C. It leaves no way to hand C a
buffer that Oak owns. This section adds exactly that, in the only shape the
borrow checker can vouch for: **a borrowed view or span becomes a pointer
and a length for the duration of one extern call, and for nothing else.**

#### 2.5.1 Argument forms

Two compiler-known functions exist only in argument position of a call to an
extern binding:

| Form | Oak operand | Yields (two consecutive parameters) | Access |
| --- | --- | --- | --- |
| `c.span_of(v)` | `v: []T` | `c.Ptr, c.Size` | C may read `len(v)` elements |
| `c.span_mut_of(s)` | `s: [*]T` | `c.Ptr, c.Size` | C may read and write `len(s)` elements |

`T` must be a fixed-width integer, a floating-point type (`20-types.md`
§11.3), `Bool`, or a `struct` whose layout is proven (`40-records.md`) and
whose fields are recursively of these types — the types with one meaning on
both sides of the boundary. Views of records without a selected
representation, of ADTs, of views, or of anything carrying a borrow are
rejected (`OAK-F0104`).

The extern binding's signature declares the pair explicitly, so the trust
boundary (§2.3) stays honest about what C receives:

```oak
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")
fread: (into: c.Ptr, size: c.Size, count: c.Size, stream: c.Ptr): c.Size = c.extern("fread")

emit: (fd: i32, bytes: []u8): i64 {
  i64(write(c.Int(fd), c.span_of(bytes)))
}

fill: (buffer: [*]u8, stream: c.Ptr): u32 {
  n: c.Size = fread(c.span_mut_of(buffer), c.Size(u32(1)), stream)
  ...
}
```

`c.span_of(bytes)` occupies **two** parameter positions — `data` and
`count` — and the checker matches them as a unit: the parameter at the
span's position must be `c.Ptr` and the next must be `c.Size`
(`OAK-F0105` otherwise). The length passed is the element count, not the
byte count; `T`'s size is known to both sides.

#### 2.5.2 Borrowing rule

For the borrow checker (`50-borrowing.md`), an extern call whose arguments
include `c.span_of(v)` is a **read use** of `v` and one including
`c.span_mut_of(s)` is a **write use** of `s`, for the extent of the call
expression: exactly the rule an ordinary Oak call taking `[]T` or `[*]T`
already gets. Consequently:

- a `span_mut_of` argument excludes every other borrow of the same owner in
  the same call (`OAK-B0104`, the existing exclusivity rule), so C never
  receives two writable aliases of one buffer, and never a writable alias
  together with a readable one;
- the pointer **cannot escape**: `c.span_of` is not an expression, has no
  type, and cannot be bound, stored, returned, or passed anywhere but an
  extern parameter position (`OAK-F0103` extended). The foreign function
  may, of course, retain the pointer — that is a foreign-contract violation
  under the trust rule of §2.3, exactly like a wrong prototype, and the
  binding's author asserts it does not happen;
- the owner outlives the call trivially, because the call is inside the
  region that proves the owner alive.

Nothing changes in the reverse direction: a `c.Ptr` returned by C is still
opaque. Oak never dereferences a foreign pointer. A program that wants C to
fill Oak memory passes Oak memory with `span_mut_of`; a program that wants
to keep a C-allocated buffer keeps the handle and asks C to operate on it.
The stronger design — a `Buffer[CpuOwned] -> Buffer[DeviceOwned]` typestate
that lets a foreign runtime *own* Oak storage for a while
(`50-borrowing.md` §11) — is the later increment, and this section is the
shape it will generalize.

#### 2.5.3 `c.String` from Oak text

A `c.String` may be constructed from a `string` **literal**: the backend
emits the literal with a trailing NUL, so `c.String("kernel_main")` is
well-formed by construction. A non-literal `string` is rejected
(`OAK-F0106`): Oak strings are not NUL-terminated and carry a length, so a
runtime `string` would need a copy the language does not perform silently
(`00-constitution.md`, no hidden work). Programs that build text at runtime
for C terminate it themselves and pass `c.span_of` over the bytes, or call a
C function that takes a pointer and a length.

#### 2.5.4 Lowering

`c.span_of(v)` lowers to the two C arguments `(void *)v.base, (size_t)v.len`
and `c.span_mut_of(s)` to `(void *)s.base, (size_t)s.len` — the base pointer
and element count of the view/span struct the backend already uses. No copy,
no allocation, no thunk. The interpreter cannot call externs (§4) and rejects
these forms with the same diagnostic it gives an extern call.

**Implemented subset.** Element types admitted today are the fixed-width
integers and `Bool`; structs with proven layouts are specified above and are
a recorded implementation gap (`STATUS.md`).

#### 2.5.5 Diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0104` | element type of a boundary span is not representable across the C ABI |
| `OAK-F0105` | `c.span_of`/`c.span_mut_of` argument does not line up with a `c.Ptr, c.Size` parameter pair |
| `OAK-F0106` | `c.String` constructed from a non-literal string |

The test runner's native adapter rules (`110-testing.md`) continue to exclude
pointer interfaces from the adapters themselves; a test may nonetheless call
an extern with a boundary span, since the span never outlives the call.

## 3. The abstract assembly interface

### 3.1 Shape

Each architecture is a compiler-known library of **instruction functions**
(`arm64` today; `x64`, `rv64` reserved). An instruction function:

- has an ordinary Oak type over fixed-width Oak integers — no `c.*` types,
  no pointers, no flags registers;
- is **total**: its result is defined for every input, using the
  architecture's own totalization where the instruction has one (ARM `CLZ` of
  zero is the operand width, and so is Oak's);
- is semantically specified in Lean (`Oak.Intrinsics`) and implemented three
  ways that must agree: the interpreter (Go), the target lowering (the real
  instruction), and the portable lowering (a branch-free C sequence).

This is the Go position: one abstract machine the programmer targets, with
per-backend realizations. Raw inline assembly, if ever admitted, will be a
separate unit form (an `asm` translation unit with a pseudo-register calling
contract, like Go's `.s` files) — never inline in Oak function bodies. That
unit form is a design direction, not part of v1.

### 3.2 v1 AArch64 catalog

| Function | Type | Instruction | Semantics |
| --- | --- | --- | --- |
| `arm64.rev32` | `(u32) -> u32` | `REV` | reverse the 4 bytes |
| `arm64.rev64` | `(u64) -> u64` | `REV` | reverse the 8 bytes |
| `arm64.rbit32` | `(u32) -> u32` | `RBIT` | reverse the 32 bits |
| `arm64.rbit64` | `(u64) -> u64` | `RBIT` | reverse the 64 bits |
| `arm64.clz32` | `(u32) -> u32` | `CLZ` | leading zeros; `clz32(0) = 32` |
| `arm64.clz64` | `(u64) -> u64` | `CLZ` | leading zeros; `clz64(0) = 64` |

Laws proven in `Oak.Intrinsics`: `rev` and `rbit` are involutions that
preserve width; `clz` is bounded by the width, hits the width exactly at
zero, and is zero exactly when the top bit is set.

### 3.3 Lowering

On an AArch64 C target the backend emits the instruction via a
`static inline` helper with inline assembly, so the guarantee is the
instruction itself. On every other target it emits a portable C99 sequence:
`__builtin_bswap` for `rev`, a guarded `__builtin_clz` (the guard supplies
the total `clz(0) = width` case the builtin leaves undefined), and the
branch-free swap network for `rbit`. Both lowerings are exercised by the
executable test suite; the interpreter implementation is the third witness.

## 4. Interpreter semantics

The interpreter implements every intrinsic (via checked host operations) so
`arm64.*` programs run identically under interpretation and compilation.
Extern bindings are **not callable** under interpretation: evaluating a call
to one is a diagnosed error, because the interpreter has no foreign world to
call into. Programs that need the boundary are native-backend programs.
