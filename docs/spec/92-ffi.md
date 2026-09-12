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
an owner. The one `c.Ptr` Oak constructs itself is **`c.null()`**, the null
pointer, for the optional pointer parameters of foreign calls
(`posix_spawn`'s file actions and attributes, `gettimeofday`'s time zone);
it is as opaque as any other `c.Ptr` and the interpreter rejects it like every
foreign pointer.

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

A symbol the C library does not provide comes from a native input the
module's manifest names — `link runtime/libmlrt.a`, `framework Metal`
(`83-modules.md` section 4.6) — which every `oak build`, `oak run`, and
`oak test` of the module passes to the C compiler.

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
does not include foreign headers (the one exception, a target constant's
header, §2.11, is why a program with target constants declares its externs
through asm labels). A mismatch between the binding and the true symbol is a
foreign-contract violation, exactly like a wrong prototype in C.

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
(`00-constitution.md`, no hidden work).

Text built at runtime reaches C through **`c.cstr(v)`**, a third argument
form in the shape of §2.5.1 (ml roadmap D1). Its operand is a named
read-only view `v: []u8` **whose last byte is NUL** — the program
terminated it — or a string literal that ends in `\0`. It stands for one
`c.String` parameter of the extern binding and yields the view's base
pointer for the duration of that call:

```oak
c_strlen: (s: c.String): c.UInt64 = c.extern("strlen")
getenv: (name: c.String): c.Ptr = c.extern("getenv")

length_of: (buffer: [8]u8): u64 {
  // buffer's last written byte is 0
  text: []u8 = view(&buffer)
  u64(c_strlen(c.cstr(text)))
}
home: (): c.Ptr = getenv(c.cstr("HOME\0"))
```

The rules are those of a boundary span, plus the terminator:

- the parameter at the argument's position must be `c.String`
  (`OAK-F0110` otherwise), and the operand a named `[]u8` view or a
  string literal (`OAK-F0110`);
- a literal operand must end in NUL, checked at compile time
  (`OAK-F0110`; `c.String("...")` terminates a literal itself and is the
  usual spelling for one);
- a view operand's terminator is checked **at the call**: the backend
  passes the pointer through a helper that traps, naming the Oak source
  position like a failed assertion, when `len(v) == 0` or
  `v[len(v) - 1] != 0`, so C never receives an unterminated buffer as a
  string. No copy is made;
- for the borrow checker the call is a read use of the view's owner for
  the call's extent, exactly as `c.span_of` (§2.5.2); the pointer cannot
  escape because `c.cstr` is not an expression (`OAK-F0103` anywhere but
  an extern parameter position), and the interpreter rejects it with the
  extern-call diagnostic (§4).

C sees `len(v) - 1` characters; the length Oak knows is not passed, which
is the point of the form — the terminator is the contract.

#### 2.5.4 Lowering

`c.span_of(v)` lowers to the two C arguments `(void *)v.base, (size_t)v.len`
and `c.span_mut_of(s)` to `(void *)s.base, (size_t)s.len` — the base pointer
and element count of the view/span struct the backend already uses. No copy,
no allocation, no thunk. `c.argv_of(bytes, slots)` (§2.5.6) lowers to a call
of the helper `oak_argv_u8`, emitted only for programs that use the form, and
`c.out(x)` (§2.5.7) to `(void *)&x`. The interpreter cannot call externs
(§4) and rejects these forms with the same diagnostic it gives an extern
call.

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
| `OAK-F0110` | `c.cstr` argument does not stand for a `c.String` parameter, its operand is not a named `[]u8` view or a string literal, or a literal operand is not NUL-terminated |
| `OAK-F0111` | `c.argv_of` argument does not stand for a `c.Ptr` parameter, or its operands are not a named `[]u8` view and a named `[*]c.Ptr` span |
| `OAK-F0112` | `c.out` argument does not stand for a `c.Ptr` parameter, or its operand is not a local binding of a `c.*` scalar type or of a declared struct with boundary fields |

#### 2.5.6 Argument vectors: `c.argv_of`

**Status: implemented and tested** (ml roadmap D4, process spawning).
`posix_spawn` and `execve` take `char *const argv[]`: a NUL-terminated array
of pointers to NUL-terminated strings. Oak has no `[]c.String` value — a
`c.String` is formed at a call and lives no longer (§2.5.3) — so the vector
is formed the same way, at the call, from storage the program owns:

```oak
posix_spawn: (pid: c.Ptr, path: c.String, actions: c.Ptr, attr: c.Ptr, argv: c.Ptr, envp: c.Ptr): c.Int = c.extern("posix_spawn")

spawn_echo: (): c.Int {
  // "echo\0" "d4\0": the strings back to back, each NUL-terminated
  words: [8]u8 = [8]u8{ 101, 99, 104, 111, 0, 100, 52, 0 }
  args: []u8 = view(&words)
  slot_storage: [4]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  no_env: [0]u8
  empty: []u8 = view(&no_env)
  env_storage: [1]c.Ptr
  env_slots: [*]c.Ptr = span(&env_storage)
  pid: c.Int = c.Int(i32(0))
  posix_spawn(c.out(pid), c.cstr("/bin/echo\0"), c.null(), c.null(), c.argv_of(args, slots), c.argv_of(empty, env_slots))
}
```

`c.argv_of(bytes, slots)` is an argument form in the shape of §2.5.1:

- it stands for one `c.Ptr` parameter of the extern binding (`OAK-F0111`
  otherwise);
- `bytes` is a named read-only view `[]u8` holding the strings back to back,
  **each NUL-terminated, the last byte of the view included**; an empty
  view is the empty vector (`{ NULL }`, the shape of an empty environment);
- `slots` is a named writable span `[*]c.Ptr` with at least one slot per
  string plus one for the trailing NULL;
- at the call the backend walks the view, stores each string's start in
  the slots, appends the NULL, and passes the slots' base; when the view
  does not end in NUL or the slots are too few it traps naming the Oak
  source position, like a failed assertion, so C never receives an
  unterminated string or an unterminated vector. The strings are not
  copied;
- for the borrow checker the call is a read use of the view's owner and a
  write use of the slots' owner for the call's extent (§2.5.2); the
  pointers cannot escape because the form is not an expression
  (`OAK-F0103` anywhere but an extern parameter position), and the
  interpreter rejects it with the extern-call diagnostic (§4).

The slots are ordinary Oak storage; after the call they hold pointers into
`bytes` that the program cannot dereference, exactly like any other `c.Ptr`.
Under §2.4's target model a `c.Ptr` slot is what `char *const argv[]`
addresses.

#### 2.5.7 Out-parameters: `c.out`

**Status: implemented and tested.** `waitpid(pid, &status, 0)`,
`posix_spawn(&pid, ...)`, `gettimeofday(&tv, NULL)`, and `clock_gettime(id,
&ts)` fill caller storage through a pointer. `c.out(x)` is the argument
form for that pointer:

```oak
waitpid: (pid: c.Int, status: c.Ptr, options: c.Int): c.Int = c.extern("waitpid")
gettimeofday: (tv: c.Ptr, tz: c.Ptr): c.Int = c.extern("gettimeofday")
Timeval: type = struct { sec: i64, usec: i64 }

exit_code: (pid: c.Int): u32 {
  status: c.Int = c.Int(i32(0))
  waited: c.Int = waitpid(pid, c.out(status), c.Int(i32(0)))
  (u32_bits_i32(i32(status)) >> u32(8)) & u32(255)
}

now: (): Timeval {
  tv: Timeval = Timeval { sec: i64(0), usec: i64(0) }
  r: c.Int = gettimeofday(c.out(tv), c.null())
  tv
}
```

- it stands for one `c.Ptr` parameter of the extern binding (`OAK-F0112`
  otherwise);
- the operand is a **local binding** of a `c.*` scalar type (never `c.Ptr`
  or `c.String`, which are not storage C fills) or of a declared `struct`
  whose fields are boundary types (§2.5.1) — the same layout guarantee a
  boundary span of structs relies on; a global is rejected (static storage
  is written only by Oak code) and so is an Oak scalar (§2.3: Oak scalars
  never cross raw; declare the binding with the `c.*` type the callee
  writes and convert after the call);
- it lowers to the binding's address for the duration of the call; for the
  borrow checker the call is a write use of the binding (§2.5.2), so a
  view or span of it cannot be live across the call;
- it is not an expression (`OAK-F0103` elsewhere) and the interpreter
  rejects it (§4).

This closed the out-pointer half of the clock gap recorded in oak #179: a
`struct timespec` declared as a boundary struct is filled through
`c.out(ts)`. The other half — `CLOCK_MONOTONIC`'s value differs between
hosts (1 on Linux, 6 on Darwin) — is a target constant (§2.11), and
`stdlib/timenative.oak` now reads both clocks through `clock_gettime` in
Oak with nothing linked but the C library.

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
| `c.borrow_string(p)` | `p: c.Ptr` to a NUL-terminated C string | `[]u8` | Oak may read the bytes before the terminator |

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

**Inbound C strings** (ml roadmap D2). `c.borrow_string(p)` is the
`c.borrow` of a string whose length C did not tell us: the view covers the
bytes before the first NUL, **excluding the terminator**, and its length is
that offset, read at runtime by scanning for the terminator (the `strlen`
contract, implemented without libc so freestanding builds stay free of
it). A NULL pointer yields the empty view — the total behaviour, chosen over
a trap because the common producers (`getenv`, optional fields) spell
"absent" as NULL, and an empty view is exactly what a program reading such
a string can do nothing wrong with; a program that must distinguish absent
from empty checks the pointer on the C side. A string longer than `u32`
holds traps. Everything else is `c.borrow[u8]`: placement (`OAK-F0107`),
scope, the recorded assumption (`OAK-B0110`, worded for the terminator: the
pointer addresses a NUL-terminated string that stays valid and unwritten
for the block's extent), lowering to the view struct over the pointer and
the scanned length, and the interpreter's rejection.

```oak
getenv: (name: c.String): c.Ptr = c.extern("getenv")

data_dir_length: (): u32 {
  p: c.Ptr = getenv(c.String("ML_DATA_DIR"))
  n: u32 = 0
  unsafe {
    dir: []u8 = c.borrow_string(p)   // empty when the variable is unset
    n = len(dir)
  }
  n
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
  only its own obligation. A strict module that accepts the contract says
  so once in its manifest, `admit OAK-B0110` (`85-discipline.md` section
  7); the warning is then recorded and listed but no longer rejects that
  module's packages. Without the admission the strict profile's
  zero-warning rule rejects every borrow (ml finding F22).
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

#### 2.7.5 Beyond one block

A borrow ends with its block. An owner that holds a foreign allocation
until the program hands it back is `Buffer[T]`, §2.8. The custody
typestate that lets a device own the memory for a while
(`Buffer[DeviceOwned]`, `50-borrowing.md` §11) is the increment after it.

#### 2.7.6 Diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0104` | element type of an inbound buffer is not representable across the C ABI |
| `OAK-F0107` | `c.borrow`/`c.borrow_mut`/`c.borrow_string` outside an `unsafe` block, or not the initializer of a named binding |
| `OAK-B0110` | (warning) the foreign buffer contract assumed for a binding |

### 2.8 Owned foreign buffers: `Buffer[T]`

**Status: implemented and tested** (`compiler/e2e_buffers_test.go`).
Motivated by the ml project's third list, item 2: weight arenas are
hundreds of megabytes, not a static array, and a `Tensor` record holding a
view over them is the frontend shape every user expects.

A borrow of §2.7 ends with its block. `Buffer[T]` is an **owner** of
runtime length: memory a runtime allocated, held by an Oak binding until
the program hands it back, and borrowed in between exactly like an owned
fixed array. It is the runtime-sized owner the arena story of
`60-effects-allocation.md` §6 needs, and the `arena` package (§2.8.4) is
the allocator over it.

#### 2.8.1 Forms

| Form | Operands | Meaning |
| --- | --- | --- |
| `b: Buffer[T] = c.own[T](p, n)` | `p: c.Ptr`, `n: u32`, inside `unsafe` | `b` owns `n` elements of `T` at `p` |
| `view(&b)`, `span(&b)` | | a read-only view / writable span of all `n` elements, tracked as borrows of `b` |
| `len(b)` | | `n` |
| `c.disown(b)` | | the `c.Ptr` back, for the runtime to free or reuse; `b` is consumed |

`T` is a boundary element type (§2.5.1), checked when the type is spelled.
`Buffer[T]` is the type of a local binding initialized by `c.own` and of
nothing else: it cannot be copied into another binding, assigned, passed as
an argument (a generic parameter included), returned, placed in a record or
array, or indexed directly. Every one of those is an error naming the
alternative, so a buffer has exactly one name and the borrow checker's
owner story holds for it: views and spans of `b` follow the rules of
`50-borrowing.md` (one writable span at a time, no writes while a view
lives, block-scoped), region-indexed functions and region records accept
`view(&b)` and `span(&b)` as they accept any owner's borrows, and nothing
derived from `b` outlives `b`'s block.

```oak
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")

Tensor[R]: type = struct { data: View[f32, R], rows: u32, cols: u32 }
tensor_of[R]: (data: View[f32, R], rows: u32, cols: u32): Tensor[R] = Tensor { data: data, rows: rows, cols: cols }

load: (count: u32): f32 {
  p: c.Ptr = malloc(c.Size(count * u32(4)))
  total: f32 = 0.0
  unsafe {
    weights: Buffer[f32] = c.own[f32](p, count)
    fill(span(&weights))
    t: Tensor = tensor_of(view(&weights), count / u32(64), u32(64))
    total = sum(t)
    free(c.disown(weights))
  }
  total
}
```

#### 2.8.2 The contract and the consumption

`c.own` admits the foreign buffer contract of §2.7.2 with a longer extent:
the memory at `p` holds `n` elements of `T` with Oak's layout, stays
mapped, and is not written by anything else, from `c.own` until
`c.disown`. It is recorded as an `OAK-B0110` assumption naming the owner.
`c.disown(b)` is rejected while any view or span of `b` is live
(`OAK-B0000`, "cannot be handed back while borrow is live"), and after it
every use of `b` — a borrow, `len`, a second `disown` — is
`OAK-B0111`, use after consumption. Freeing is the runtime's: the program
passes the returned pointer to whatever allocated it. A buffer that is
never disowned is a leak, not unsoundness; the discipline profiles may
later require the pair.

#### 2.8.3 Lowering and interpretation

`Buffer[T]` lowers to the span struct `{ T *base; u32 len }`; `c.own` fills
it, `view(&b)`/`span(&b)` copy the pair into the view or span struct,
`len(b)` reads `len`, and `c.disown(b)` reads `base`. No copy of the
memory, no allocation, no destructor. Every element access goes through
the bounds-checked view and span helpers against `n`. The interpreter has
no foreign memory and rejects `c.own` and `c.disown`.

#### 2.8.4 Arenas over a buffer (`import("arena")`)

`stdlib/arena.oak` is bump allocation over an owner's element index space:
an `Arena { used, capacity }` hands out **offsets**, never memory.
`arena_reserve(a, count, align)` returns a `Reservation { ok, offset,
arena }` — the aligned start of a range that fits after every earlier
reservation, and the arena after it, or `ok = false` with the arena
unchanged; `arena_align_up` rounds without wrapping (an offset that cannot
be rounded becomes the largest `u32`, which no capacity admits);
`arena_reset` and `arena_remaining` complete the surface. The program
carves the ranges it reserved with `subslice` over `view(&b)` or
`span(&b)`, so the borrow checker's rules decide what may be live at once:
any number of views, or one span and its reborrows. Everything is `u32`
arithmetic that the interpreter and the backends compute identically.

#### 2.8.5 What stays outside

A `Buffer[T]` in a record or a global (a `Weights` record owning its
arena, a package-level buffer loaded once) needs the record to carry
custody, which is the `Buffer[CpuOwned]` typestate of `50-borrowing.md`
§11 and the resource-consumption machinery of §9 applied to a field. The
element-space arena admits one span at a time; carving several writable
ranges from one buffer at once is the disjoint-region proof of
`50-borrowing.md` §6, or an `unsafe` disjointness assumption.

#### 2.8.6 Diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0107` | `c.own` outside an `unsafe` block, or not the initializer of a named binding |
| `OAK-B0110` | (warning) the foreign buffer contract assumed for an owner |
| `OAK-B0111` | a buffer used after `c.disown` |
| `OAK-B0000` | `c.disown` while a view or span of the buffer is live |

### 2.9 C ABI exports from any package

Status: implemented (`export("symbol")`, `OAK-F0108`, `OAK-F0109`).

The C header of a build (`oak build -header out.h`, §2.6) lists the root
package's `pub` functions under `oak_<name>`. That rule alone puts every C
ABI entry point of a program into the root package: a numeric runtime whose
kernels, checks, and benchmarks are all C-callable grows a root file of
thousands of lines. An **export marker** lets a `pub` function of *any*
package name its own C symbol:

```oak
package ops

export("oak_ml_add") pub add: (a: i32, b: i32): i32 = a + b
```

#### 2.9.1 Grammar and meaning

`export("symbol")` precedes a `pub` function declaration; `export` is a
contextual identifier, so `export := 1` stays an ordinary binding. The symbol
is a string literal that must satisfy the C identifier grammar of §2.3
(`OAK-F0102`'s pattern). The marked function is defined in the generated C
under the elaborator's internal name for every Oak caller, and additionally
under `symbol` as a forwarding function the C compiler inlines; both the
prototype and the header carry `symbol` with the function's parameter and
result types spelled exactly as §2.6 spells them for the root's exports
(records as their typedefs, owned arrays as wrapper structs, views and spans
as the view and span structs, a variadic tail as a view). The forwarding
wrapper is the only C-visible name the marker adds; nothing about the Oak
name, visibility, or calling convention of the function changes.

#### 2.9.2 What the header lists

The header has two parts, each deterministic:

1. the root package's `pub` functions under `oak_<name>`, in declaration
   order, as before — a root `pub` function **with** a marker appears under
   its symbol only (the marker replaces the implicit name in the header; the
   generated C still defines `oak_<name>` for the root's own callers);
2. every explicit export of the program, from any package, sorted by symbol,
   each preceded by a comment naming its package and Oak name.

A dependency's `pub` functions without a marker are **not** part of the C
surface. Before this section they leaked into the header under the
elaborator's internal names (`oak_example_dcom_sml_sops__add`), which embed
the module path and are stable for nobody; the marker is now the only way a
non-root function reaches the header. Exports of a dependency *module*
appear when the root module imports the package (transitively), because the
build compiles exactly the packages it reaches; a package that is not
reached contributes no code and no exports.

Types named by an exported signature are emitted the way the C file emits
them: a root type as `oak_Name`, a dependency type under its internal name.
Exporting a type under a chosen C name is a separate request (a
`export("...")` marker on a type declaration) and is not provided here.

#### 2.9.3 Rules and diagnostics

| Code | Meaning |
| --- | --- |
| `OAK-F0108` | two exports would share one C symbol: two markers, or a marker and a root `pub` function's implicit `oak_<name>`; the diagnostic names both functions and their packages |
| `OAK-F0109` | the marker's symbol is not a C identifier, or the function has no single C ABI shape: not `pub`, a method, an extern binding (its foreign symbol is already its C name), or a generic template (export a concrete wrapper instead) |

The parser rejects a marker that is not followed by a `pub` function
declaration (a value, a type, a private function). Symbols are program-unique
because the C linker has one namespace: the check runs over the elaborated
program, so exports of every reached package are compared together with the
root's implicit exports. A signature the header cannot represent (a string,
a closure) is rejected when the header is emitted, as for root exports
(§2.6).

#### 2.9.4 API snapshots

An explicit export is part of a package's public surface: the snapshot
(`82-package-semver.md`) records the symbol as the function's ABI identity
(`c-export <symbol>`), so renaming or removing an export is a major change
and adding a marker to a published function is classified as an ABI change
too — conservative, since a consumer linking the old symbol set is unaffected
by an addition, but the snapshot laws classify any ABI difference as major.

### 2.10 Calls through a foreign function pointer

Status: implemented (`c.Fn[...]`, `c.fn_at`, `OAK-F0113`, `OAK-B0122`;
`compiler/e2e_ffi_fnptr_test.go`). Motivated by ml roadmap D3: a `c.Ptr`
from `dlsym` invoked with a declared signature, so the runtime's dispatch
loop over compiled kernels can move out of Zig.

An extern binding (§2.3) names a symbol the linker resolves. A function
whose address is known only at run time — a kernel `dlsym` found in a
library `dlopen` loaded — has no symbol Oak can name. This section gives it
a **declared signature and a scope** instead, in the shape of §2.7: a
foreign pointer becomes a callable value for the extent of one unsafe block,
under a contract the program states, and for nothing else.

#### 2.10.1 The type and the form

`c.Fn[(params) -> ret]` is the type of a foreign function of the given
signature. Its parameter types and its return type obey exactly the extern
rule (§2.3, `OAK-F0101`): `c.*` types, proven-layout structs by value, and
`()` for the return. The type exists in one position only — the annotation
of a local binding, inside an `unsafe` block, that `c.fn_at` initializes:

```oak
dlopen: (path: c.Ptr, mode: c.Int): c.Ptr = c.extern("dlopen")
dlsym: (handle: c.Ptr, name: c.String): c.Ptr = c.extern("dlsym")

kernel_length: (text: []u8): u64 {
  handle: c.Ptr = dlopen(c.null(), c.Int(i32(2)))
  p: c.Ptr = dlsym(handle, c.String("strlen"))
  n: u64 = 0
  unsafe {
    strlen_at: c.Fn[(c.String) -> c.UInt64] = c.fn_at(p)
    n = u64(strlen_at(c.cstr(text)))
  }
  n
}
```

- `c.fn_at(p)` takes one `c.Ptr` and is admitted only inside an `unsafe`
  block, as the initializer of a named binding (`OAK-F0107`, the placement
  rule of `c.borrow`), and that binding must carry a `c.Fn` annotation
  (`OAK-F0113`): the annotation *is* the declared ABI, as an extern binding's
  signature is; Oak never infers a foreign signature.
- `c.Fn` anywhere else — a record field, a global, a parameter, a return
  type, an array element, a binding outside `unsafe` or without `c.fn_at` —
  is `OAK-F0113`. A foreign function pointer never crosses back into Oak
  semantics: it is not an Oak function value, cannot be captured, compared,
  stored, or passed to Oak code, and is dropped when its block ends.
- A signature naming a type that cannot cross the boundary (an Oak scalar,
  a view, a string) is `OAK-F0113` at that type.

#### 2.10.2 Calls

A call `f(args)` through a `c.Fn` binding is checked **exactly as a call to
an extern binding of the annotated signature**: the same argument forms
(`c.span_of`/`c.span_mut_of` §2.5.2, `c.cstr` §2.5.3, `c.argv_of` §2.5.6,
`c.out` §2.5.7, `c.null()`, `c.*` scalars, structs by value), the same
arity and type rules, the same borrow uses for the call's extent. The
backend lowers the binding to an opaque pointer and every call to a cast
and a call, `((ret (*)(params))f)(args)`, with each C spelling taken from
the same table extern prototypes use — so the cast is precisely the
prototype an extern binding of that signature would have declared, and no
program text reaches the generated C except through that table.

**Effects.** The effect checker (`60-effects-allocation.md`) cannot know
what a function at a run-time address does; a call through a `c.Fn` binding
is a call through a function value whose effects nothing declares, so a
function that `forbids` any effect and reaches such a call fails closed with
`OAK-E0103`, exactly as a call through an Oak function value does. A
declared-effects form for foreign pointers is deliberately not provided in
this increment.

#### 2.10.3 The contract, recorded

`c.fn_at` is a trust assumption of the same kind as `c.borrow`'s (§2.7): the
program asserts that the pointer is a function of the annotated signature,
callable for the block's extent. The borrow checker records it on every
binding as **`OAK-B0122`**, a warning with the recorded-assumption
treatment: `oak vet` and the REPL's `:obligations` list it, the strict
profile rejects the module unless its `oak.mod` says `admit OAK-B0122`
(`85-discipline.md` §7), and admitting the foreign-buffer contract
(`OAK-B0110`) does not admit this one — they are different claims about
different things. The one check the compiler can make it makes: `c.fn_at`
of a NULL pointer traps at the conversion, naming the Oak source position
as an assertion does, so a call through the binding never dereferences NULL.

The interpreter rejects `c.fn_at` (it has no foreign code to call), as it
rejects every native-only form (§4).

### 2.11 Target constants

Status: implemented (`c.const`, `OAK-F0114`; `compiler/e2e_ffi_const_test.go`;
`stdlib/timenative.oak` is the first consumer). Motivated by oak #211 and
ml roadmap D6: the runtime-in-Oak touches `CLOCK_MONOTONIC`, `O_RDONLY`,
`SEEK_SET`, `EINTR`, `PROT_READ`, the signal numbers — values a C header
defines and every target defines differently.

A **target constant** is a top-level binding whose value is a C constant
the target's headers define:

```oak
CLOCK_REALTIME: c.Int = c.const("CLOCK_REALTIME", "<time.h>")
CLOCK_MONOTONIC: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
clock_gettime: (id: c.Int, ts: c.Ptr): c.Int effects { Os.Syscall } = c.extern("clock_gettime")
Timespec: type = struct { sec: i64, nsec: i64 }

monotonic_nanos: (): i64 {
  ts: Timespec = Timespec { sec: i64(0), nsec: i64(0) }
  r: c.Int = clock_gettime(CLOCK_MONOTONIC, c.out(ts))
  i32(r) != i32(0) ? { i64(0) } | { ts.sec * i64(1000000000) + ts.nsec }
}
```

Oak never learns the value. The C backend emits the identifier and the C
compiler resolves it for the target it compiles for — `CLOCK_MONOTONIC` is 1
on Linux and 6 on Darwin, and the same Oak source is right on both. What Oak
checks is the shape, and the shape is what makes the emission injection-free.

#### 2.11.1 The form

- `NAME: c.T = c.const("IDENTIFIER", "HEADER")` is admitted **only as a
  top-level binding with an explicit `c.*` integer annotation** — `c.Int`,
  `c.UInt`, `c.Int32`, `c.UInt32`, `c.Int64`, `c.UInt64`, `c.Long`,
  `c.ULong`, `c.Size`. A local binding, an expression position, an Oak
  type, `c.Ptr`, or `c.String` is `OAK-F0114` (pointers and strings are not
  constants a header spells; floats have no boundary constants in this
  increment).
- The identifier is a string literal satisfying the C identifier grammar
  of `OAK-F0102` (`[A-Za-z_][A-Za-z0-9_]*`); the header is a string literal
  spelled `<name.h>`, `<dir/name.h>`, or `"name.h"` — identifier characters,
  dots, hyphens, and slashes, no `..` segment. Anything else is `OAK-F0114`.
  Both are re-validated in the backend before they reach the generated
  source, as extern symbols are.
- The binding is read-only: assignment to it is `OAK-F0114`. It is **not a
  compile-time constant for Oak**: a later global initialized from it is the
  ordinary `OAK-T0501` case (a C `static const` is not a constant
  expression either), and the layout builtins do not fold it.
- Reading it is ordinary safe Oak — a `c.Int` value that converts through
  the §2.2 rows or passes at a `c.Int` extern parameter, as above.

#### 2.11.2 What the backend emits

At the head of the generated C, before every other header, the program's
distinct target-constant headers are included, preceded by a POSIX.1-2008
feature-test macro when none is defined (strict `-std=c99` builds on glibc
otherwise withhold `clock_gettime` and the `CLOCK_*` identifiers from
`<time.h>`); a freestanding build (`OAK_FREESTANDING`, or a non-hosted
compiler) fails with an `#error`, because a target constant needs the
target's headers. Each constant is a file-scope
`static const int oak_const_NAME = IDENTIFIER;` — the initializer is the
header's definition, a constant expression on the target; the `oak_const_`
prefix keeps the binding clear of the identifier itself, which on Darwin is a
macro over an enumerator.

A foreign header may declare functions the program also binds with
`c.extern` — `<time.h>` declares `clock_gettime` — and Oak's own prototype
for that binding would then be a conflicting redeclaration. So **in a program
with target constants every extern binding is declared under Oak's own
identifier bound to the symbol by an asm label**:

```c
extern int oak_extern_clock_gettime( int id, void * ts ) __asm__(OAK_ASM_SYMBOL("clock_gettime"));
```

with `OAK_ASM_SYMBOL` prepending the target's `__USER_LABEL_PREFIX__`
(`_` on Darwin, nothing on Linux), and every call names
`oak_extern_clock_gettime`. The prototype Oak asserts is unchanged, the
header's declaration stands beside it untouched, and the linker still binds
the one symbol. A program without target constants emits the plain
prototype it always did, so no other program's C changes.

#### 2.11.3 Elsewhere

The interpreter rejects `c.const` (it has no target whose headers define the
value, §4). The Lean extraction renders the binding as an `opaque` constant
of the `c.*` scalar's Lean type (`95-extraction.md` §3): a theorem about a
function that reads it holds for every value, which is exactly the claim the
program makes. A target constant carries no effect and records no
assumption — the trust it asks for is the extern rule's (§2.3): that the
named header defines the named identifier with the annotated type is the
author's assertion, checked by the C compiler as far as C checks it (an
undefined identifier fails the build; a wrong width converts silently, as a
wrong extern prototype would).

### 2.12 Objective-C message sends

Status: implemented (`c.msg_send`, `OAK-F0115`, `OAK-B0122`;
`compiler/e2e_ffi_objc_test.go`; `stdlib/objc.oak`). Motivated by ml
roadmap D5: Metal in Oak — device, library, pipeline, encoder, dispatch,
sync — is seven hundred lines of Objective-C message sends, and every one
of them is a call to `objc_msgSend` under a signature the caller knows and
the runtime does not check. Zig spells that as a cast of `objc_msgSend` to
a function pointer type; this section gives Oak the same thing with the
signature checked at the call, and nothing more. Oak learns no
Objective-C: a class, an instance, and a selector are opaque `c.Ptr`
values, resolved by the runtime's own functions (`objc_getClass`,
`sel_registerName`, ordinary externs the `objc` package declares), and
every send states its own ABI.

#### 2.12.1 The form

```oak
import("objc")

length_of: (text: []u8): u64 {
  string_class: c.Ptr = objc.objc_class(str_bytes("NSString\0"))
  alloc: c.Ptr = objc.objc_sel(str_bytes("alloc\0"))
  init_utf8: c.Ptr = objc.objc_sel(str_bytes("initWithUTF8String:\0"))
  length: c.Ptr = objc.objc_sel(str_bytes("length\0"))
  n: u64 = 0
  unsafe {
    fresh: c.Ptr = c.msg_send[() -> c.Ptr](string_class, alloc)
    s: c.Ptr = c.msg_send[(c.String) -> c.Ptr](fresh, init_utf8, c.cstr(text))
    n = u64(c.msg_send[() -> c.UInt64](s, length))
  }
  n
}
```

`c.msg_send[(params) -> ret](receiver, selector, args...)` is a call and
only a call: the bracket carries a boundary function type — the one place a
function type appears in expression position, and the parser reads it with
the type grammar — and the parenthesized list starts with the receiver
(`id`) and the selector (`SEL`), both `c.Ptr`, followed by exactly the
declared arguments.

- The bracketed signature obeys the extern rule (§2.3, `OAK-F0101`) as a
  `c.Fn` signature does (§2.10): `c.*` types and proven-layout structs by
  value for the parameters, those or `()` for the return; a type that
  cannot cross the boundary is `OAK-F0113` at that type. A struct return by
  value (`NSRange`, `MTLSize`) is admitted, because on arm64 it comes back
  through the same entry point (below).
- The call is checked **exactly as a call to an extern binding of type
  `(c.Ptr, c.Ptr, params) -> ret`**: the same argument forms (`c.span_of`,
  `c.cstr`, `c.argv_of`, `c.out`, `c.null()`, scalars, structs), the same
  arity and type rules, the same borrow uses for the call's extent. The
  receiver and the selector are the two leading pointers; there is no
  Oak-side notion of which class answers which selector.
- `c.msg_send` is admitted only inside an `unsafe` block (`OAK-F0115`), only
  as the callee of a call; the bracket must be a function type and the call
  must name at least the receiver and selector (`OAK-F0115`); `c.msg_send`
  without its bracket is `OAK-F0115` with the form spelled out.
- **arm64 only, in this increment.** On arm64 every message goes through
  `objc_msgSend` itself; other Objective-C targets route struct returns
  through `objc_msgSend_stret` and floating-point returns through
  `objc_msgSend_fpret`, and this form does not select among them. The
  backend emits an `#error` for any other target, so a program that sends
  messages fails to build rather than misdispatching; the receiver-and-
  selector prefix and the checked signature are target-independent, so
  lifting the restriction is a backend change alone.

#### 2.12.2 Lowering

The backend declares the runtime's entry point once per program that sends
messages, with no prototype — `extern void objc_msgSend(void);` — and
lowers every send to a cast and a call:

```c
(( uint64_t (*)( void *, void * ) )( objc_msgSend ))( s, length )
(( void * (*)( void *, void *, const char * ) )( objc_msgSend ))( fresh, init_utf8, oak_cstr_u8( text, "main.oak", 12 ) )
```

Each C spelling comes from the same table extern prototypes use, so the cast
is precisely the prototype an extern binding of `(c.Ptr, c.Ptr, params) ->
ret` would have declared. The runtime library itself is not a link input
Oak names: the framework the module declares (`framework Foundation`,
`framework Metal`; `83-modules.md` §4.6) brings `libobjc` with it. A program
without message sends emits no mention of `objc_msgSend`.

#### 2.12.3 The contract, recorded

A send asserts that the selector's implementation on that receiver has the
bracketed signature — the same kind of claim `c.fn_at` makes about a pointer
(§2.10.3), made per call rather than per binding. The borrow checker records
every send as **`OAK-B0122`**, worded for the selector, with the
recorded-assumption treatment: `oak vet` and `:obligations` list it, the
strict profile rejects the module unless its `oak.mod` says `admit
OAK-B0122` (`85-discipline.md` §7), and the one admission covers both forms
because they are the one claim — a foreign function of a declared
signature — while `admit OAK-B0110` covers neither. The effect checker
treats a send as a call through a function value whose effects nothing
declares: a function that `forbids` any effect and reaches one fails closed
with `OAK-E0103` (`60-effects-allocation.md`). The runtime's nil-receiver
rule (a message to NULL returns zero) is the runtime's; Oak does not check
the receiver.

The interpreter rejects `c.msg_send` (it has no Objective-C runtime, §4),
before evaluating the arguments. The Lean extraction fails closed on it, as
on every foreign call (`95-extraction.md` §4).

#### 2.12.4 The `objc` package

`stdlib/objc.oak` (`import("objc")`, Darwin-only, library package) declares
the runtime's lookups as ordinary externs and wraps them for Oak bytes:
`objc_class(name)` (`objc_getClass` over `c.cstr` of a NUL-terminated view)
and `objc_sel(name)` (`sel_registerName`). It deliberately models nothing
else: no class hierarchy, no method signatures, no retain/release policy —
those are the sender's, stated at each `c.msg_send`. Metal itself is not
attempted here; `compiler/e2e_ffi_objc_test.go` drives Foundation
(`NSString` length, `NSNumber` round trip, an `NSRange` returned by value
through `NSValue`) as the acceptance case.

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
