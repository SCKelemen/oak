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
`Oak.CInterop` (Lean) proves the mapping is injective and round-trips. The
`f32`/`f64` rows are implemented as bit-preserving casts between the same
IEEE formats (`20-types.md` §11.3.4); `f16`/`bf16` have no `c` counterpart
and cross as `u16` bit patterns.
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
  binding must be a `c.*` type, **or a declared `struct` (or boundary tagged
  union, §2.6) whose fields are boundary types (§2.5.1), passed by value**.
  Oak scalars never cross the boundary raw; a struct crosses with the layout
  the backend asserts at C compile time, in both directions — `div` from
  libc returning its `div_t` by value, or a Metal launch descriptor handed
  to a runtime shim, both without a pointer.
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
§11.3; the `f16`/`bf16` storage formats cross as their `uint16_t`
carriers and `f8e4m3`/`f8e5m2` as `uint8_t`), `Bool`, a boundary tagged union (§2.6), or a `struct` whose
layout is proven (`40-records.md`) and whose fields are recursively of
these types — the types with one meaning on both sides of the boundary. Views of records without a selected
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

**Implemented.** Every element type of §2.5.1 is admitted: fixed-width
integers, `f32`/`f64` and the `f16`/`bf16`/`f8e4m3`/`f8e5m2` storage
formats, `Bool`, tagged
unions whose payloads are boundary types (§2.6), and declared `struct`
types whose fields are recursively boundary types (the backend emits these
with C compile-time size and offset assertions, so the pointer C receives
addresses exactly the layout it expects). Semantic records without the
`struct` keyword, strings, views, and spans are rejected (`OAK-F0104`).

#### 2.5.5 Diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0104` | element type of a boundary span is not representable across the C ABI |
| `OAK-F0105` | `c.span_of`/`c.span_mut_of` argument does not line up with a `c.Ptr, c.Size` parameter pair |
| `OAK-F0106` | `c.String` constructed from a non-literal string |

The test runner's native adapter rules (`110-testing.md`) continue to exclude
pointer interfaces from the adapters themselves; a test may nonetheless call
an extern with a boundary span, since the span never outlives the call.

### 2.6 Tagged unions at the boundary

**Status: implemented and tested.** Motivated by the hypervisor ports, whose
effect-returning modules (`ipc`, `virtio_mmio`) flattened a union with data
into a status code plus out-parameter globals because the union had no shape
C could be told about.

A declared tagged union (`30-adts-patterns.md`) has exactly one C
representation, and the backend asserts it at C compile time:

```c
typedef struct oak_Effect {
  u32 tag;                       /* the variant's declaration index */
  union { u32 Send; u8 Yield; } payload;
} oak_Effect;
typedef char oak_union_layout_Effect[ (sizeof(oak_Effect) == 8u && _Alignof(oak_Effect) == 4u
  && offsetof(oak_Effect, tag) == 0u && offsetof(oak_Effect, payload) == 4u) ? 1 : -1 ];
```

- The **tag** is a fixed-width `u32` holding the variant's declaration index
  (`None | Send: u32 | Yield: u8` numbers them 0, 1, 2). A C `enum` is still
  emitted to name the values, but the member is not of enum type: an enum's
  width is implementation-defined, and the tag's is not.
- The **payload** is a C union of the payloads, named by variant, at the
  first offset aligned for its strictest member. A union without payloads is
  the tag alone.
- The **layout** is `semir.TaggedUnionLayout`: the union is the largest
  payload rounded up to the strictest alignment, and tag plus union are
  placed by the natural record layout (`40-records.md` §6, the Lean-refined
  algorithm). The typedef assertion makes cc ratify the numbers, exactly as
  for records. A union with a payload the layout model cannot place (a
  `string`, a view, a record without a proven layout) is emitted without an
  assertion: it is fine inside Oak and has no proven shape at the boundary.

What the proven shape buys:

- **Exported functions.** A `pub` function returning or taking a tagged union
  is C-callable as is. `oak build -header out.h` (`Compilation.EmitHeader()`)
  emits the C header of the exported surface: the generated C's typedefs,
  every declared type in dependency order with its layout assertions —
  records, tagged unions, array wrappers, views and spans — emitted by the
  same emitters as the C file so the two cannot disagree, and one prototype
  per `pub` function (private functions, helpers, globals, and bodies are not
  part of the surface). A consumer includes the header and links the
  generated C, reading `e.tag` (the enum constants `oak_Effect_tag_Send`
  name the values) and `e.payload.Send`. A hand-written mirror struct with
  the same member types remains ABI-identical on the recorded targets.
- **Layout builtins.** `size_of[Effect]()`, `align_of[Effect]()`, and
  `offset_of[Effect](tag)` / `offset_of[Effect](payload)` are admitted
  (`40-records.md` §6b) so a C mirror can be pinned with `static_assert`.
- **Records.** A record field of tagged-union type is placeable once the
  union's layout is proven, and the union is emitted ahead of the record
  (`codegen/mono.go`); this is the same mechanism nullable fields
  (`Option[T]`) already used, generalized to every declared union.
- **Boundary spans.** `c.span_of` / `c.span_mut_of` admit views and spans of
  tagged unions whose payloads are fixed-width integers, `Bool`, or such
  unions (§2.5.1); other payloads are rejected with `OAK-F0104`.

Generic unions cross only as concrete instantiations named by a declared
alias or field; a template has no representation. The interpreter has no
struct layout and treats the builtins as compiled-backend facts (§6b).

### 2.7 Inbound buffers: borrowing runtime-owned memory

**Status: implemented and tested** (`compiler/e2e_ffi_inbound_test.go`).
Motivated by the ml project's third list: every upload, readback, host-side
conversion, and test comparison stayed in Zig because Oak had no way to see
memory a runtime owns (`docs/notes/ml-feedback-2026-09.md`, tier 9).

§2.5 hands Oak memory to C for one call. This section is its inverse, in
the same shape the borrow checker can vouch for: **a foreign pointer and a
count become a borrowed view or span for the extent of one unsafe block,
under a contract the program states, and for nothing else.**

#### 2.7.1 Forms

Two compiler-known forms exist only as the initializer of a named binding
inside an `unsafe` block:

| Form | Operands | Yields | Access |
| --- | --- | --- | --- |
| `c.borrow[T](p, n)` | `p: c.Ptr`, `n: u32` | `[]T` | Oak may read `n` elements |
| `c.borrow_mut[T](p, n)` | `p: c.Ptr`, `n: u32` | `[*]T` | Oak may read and write `n` elements |

`T` is a boundary element type exactly as in §2.5.1 — a fixed-width
integer, a floating-point or storage format, `Bool`, a boundary tagged
union, or a proven-layout `struct` of those — so the elements have one
meaning on both sides (`OAK-F0104` otherwise). `n` is a `u32` element
count, never a byte count, and lengths stay in `u32` on the Oak side
(§2.2). The result is an ordinary view or span: indexing is bounds-checked
against `n`, `len` reads `n`, `subslice` derives within it, and it may be
passed to any Oak function taking `[]T`/`[*]T`.

```oak
device_buffer: (id: u32): c.Ptr = c.extern("rt_buffer_host_ptr")
device_len: (id: u32): u32 = c.extern("rt_buffer_len")

readback_sum: (id: u32): f32 {
  p: c.Ptr = device_buffer(id)
  total: f32 = 0.0
  unsafe {
    values: []f32 = c.borrow[f32](p, device_len(id))
    i: u32 = 0
    while i < len(values) {
      total = total + values[i]
      i = i + u32(1)
    }
  }
  total
}
```

#### 2.7.2 The trust contract

`unsafe` marks where an assumption is admitted (`00-constitution.md`,
`Oak.Unsafe`). An inbound borrow admits exactly one, the **foreign buffer
contract**, which the program asserts for the block's extent:

1. `p` addresses at least `n` elements of `T`, laid out as Oak lays out
   `T` (the natural layout the backend asserts for proven structs);
2. the memory stays mapped and is not freed, moved, or resized while the
   block runs;
3. for `c.borrow_mut`, nothing else writes the memory while the block runs
   and no other live borrow in the block aliases it; for `c.borrow`,
   nothing writes it.

The contract is the binding author's, exactly as an extern prototype is
(§2.3): a runtime that breaks it breaks the program, and Oak's guarantees
end there. What Oak does guarantee is everything else: the borrow cannot
outlive the block, every access is bounds-checked against `n`, the
element type is one both sides agree on, and the assumption is recorded.

#### 2.7.3 Rules and checking

- **Placement.** Outside an `unsafe` block, or anywhere but the initializer
  of a named binding (a call argument, a return, a field), the form is
  rejected (`OAK-F0107`). The binding gives the borrow a scope.
- **Scope.** The borrow checker treats the binding as a borrow of a foreign
  owner that lives exactly as long as the enclosing block. The view or span
  is dropped at the block's end; an `unsafe` block is a statement, so the
  only ways out are assigning the borrow (or a reborrow of it, including
  one returned by a region-indexed call) to an outer binding or storing it
  in an aggregate, and the existing rules reject both (`OAK-B0105`,
  `OAK-B0109`).
- **Recorded assumption.** An accepted borrow records the foreign buffer
  contract as an `OAK-B0110` warning naming the binding, next to every
  other admitted unsafe assumption, so an audit of a program's assumptions
  lists its foreign borrows. `Oak.Unsafe` (Lean) carries the contract as
  the second entry of the assumption vocabulary and proves it discharges
  only its own obligation.
- **Exclusivity.** Two `c.borrow_mut` bindings in one block over the same
  memory are the program's contract violation (item 3), not something Oak
  can see: distinct foreign owners are distinct to the checker. Two views
  are fine. A span and a view of the same pointer in one block are the
  same violation.

#### 2.7.4 Lowering and interpretation

`c.borrow[T](p, n)` lowers to the view struct `{ (const T *)p, (u32)n }`
and `c.borrow_mut[T](p, n)` to the span struct `{ (T *)p, (u32)n }` — the
representation every view and span already has, so every existing helper
(bounds-checked indexing, `subslice`, `len`) applies unchanged. No copy, no
allocation. The interpreter has no foreign memory and rejects the forms
with the diagnostic it gives an extern call (§4).

#### 2.7.5 What this is not yet

A borrow ends with its block. A `Buffer[CpuOwned]` record that *owns* a
foreign allocation across calls, hands it to a device (`Buffer[DeviceOwned]`)
and gets it back, is the typestate of `50-borrowing.md` §11: it needs the
record to carry the region (`50-borrowing.md` §8c, more than one region per
record) and an explicit close. This section is the shape that record's
methods will use internally; the tier-9 note records it as the next
increment after runtime-sized arenas.

#### 2.7.6 Diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0104` | element type of an inbound buffer is not representable across the C ABI |
| `OAK-F0107` | `c.borrow`/`c.borrow_mut` outside an `unsafe` block, or not the initializer of a named binding |
| `OAK-B0110` | (warning) the foreign buffer contract assumed for a binding |

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
