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
