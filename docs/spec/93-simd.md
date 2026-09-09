# Portable SIMD and Architecture Vector Instructions

Oak's SIMD story follows the abstract-machine rule of `92-ffi.md` §3, in the
style of Go's portable `simd` package: **one portable vector library with
total, exactly specified lane semantics**, realized by each backend as the
target's vector instructions where they exist and as proven-equivalent
portable scalar code where they do not. Architecture libraries (`arm64`)
additionally expose the instructions that have no portable meaning worth
abstracting (horizontal reductions, lane population counts) as ordinary
typed functions over the same vector types.

## 1. The `simd` library

`simd` is a compiler-known library with the same name rules as `c` and
`arm64` (`92-ffi.md` §2): type position always resolves the library; a local
binding named `simd` shadows it in expression position.

### 1.1 Vector types

v1 defines the 128-bit unsigned integer vectors:

| Type | Lanes | Lane type |
| --- | --- | --- |
| `simd.U8x16` | 16 | `u8` |
| `simd.U16x8` | 8 | `u16` |
| `simd.U32x4` | 4 | `u32` |
| `simd.U64x2` | 2 | `u64` |

A vector is an ordinary 16-byte **value**: copyable, stack-resident, no
borrow interaction, no implicit conversion between vector types or to
scalars. Lane order is index order; lane `0` is the first element loaded
from memory (memory order matches view element order, independent of host
endianness at the semantic level).

Signed, float, and wider vectors are reserved for later revisions; the
naming (`I32x4`, `F32x4`, 256-bit `U8x32`) is fixed now so programs and
backends do not fork conventions. The floating-point vectors `F32x4` and
`F64x2` are specified with the floating-point types themselves
(`20-types.md` §11.3.7): lane-wise `add sub mul div fma min max sqrt neg abs`
under the fixed IEEE semantics of §11.3.3, lane extract and insert, and a
horizontal `reduce_add` whose pairwise-tree grouping is its semantics.

### 1.2 Operations

For each vector type `E` with lane type `uN` and lane count `L` (spelled
with its type suffix, e.g. `simd.add_u8x16`):

| Function | Type | Semantics |
| --- | --- | --- |
| `simd.splat_E` | `(uN) -> E` | every lane is the operand |
| `simd.load_E` | `([]uN, u32) -> E` | lanes `v[off] .. v[off+L-1]`; **traps** unless `off + L ≤ len(v)` |
| `simd.store_E` | `([*]uN, u32, E) -> ()` | stores the `L` lanes; **traps** unless `off + L ≤ len(s)` |
| `simd.add_E` / `simd.sub_E` | `(E, E) -> E` | lane-wise, wrapping mod `2^N` |
| `simd.and_E` / `simd.or_E` / `simd.xor_E` | `(E, E) -> E` | lane-wise bitwise |
| `simd.min_E` / `simd.max_E` | `(E, E) -> E` | lane-wise unsigned |
| `simd.eq_E` | `(E, E) -> E` | mask: lane is all-ones where equal, zero where not |
| `simd.any_E` | `(E) -> Bool` | true iff **some** lane is nonzero |
| `simd.all_E` | `(E) -> Bool` | true iff **every** lane is nonzero |

Every operation is **total** — no lane produces undefined behavior for any
input — and loads/stores carry the same never-UB obligation as scalar
view/span access (`50-borrowing`): out-of-range offsets trap. Offsets are
in **elements**, not bytes. Unaligned element access is legal; the backend
is responsible for unaligned-safe lowering.

`eq` masks compose with the bitwise operations and reduce with `any`/`all`:
`simd.any_u8x16(simd.eq_u8x16(chunk, simd.splat_u8x16(needle)))` is the
canonical byte-search kernel, and its law — the reduction is true exactly
when some lane matches — is proven in `Oak.Simd`.

### 1.3 Formal model

`Oak.Simd` (Lean) models a vector as its lane list and proves, for the v1
catalog: splat yields constant lanes of exact count; the binary operations
are pointwise and preserve lane count; wrapping arithmetic is arithmetic
mod `2^N`; `eq` masks are two-valued (each lane exactly zero or all-ones,
all-ones iff the operand lanes are equal); `any ∘ eq` holds iff some lane
pair matches; `all ∘ eq` holds iff the vectors are equal; and a store
followed by a load of the same region returns the stored vector while
leaving every other element untouched.

### 1.4 Lowering

On AArch64 each operation lowers to its NEON instruction through one
`static inline` helper (`vld1q`/`vst1q`, `vaddq`, `vceqq`, `vmaxvq`, …);
elsewhere it lowers to a portable C99 lane loop with the same semantics.
The vector representation is one C struct (a lane array) for both
lowerings, so the ABI never depends on which path was taken. Both lowerings
run in the executable test suite (`-DOAK_PORTABLE_INTRINSICS` forces the
portable path); the interpreter is the third witness. NEON gaps are closed
with equivalent instruction sequences (64-bit lane `min`/`max` via
compare-and-select; `all` over 64-bit lanes via per-lane extraction) — the
portable semantics are the specification, the instruction selection is not.

## 2. arm64 vector instruction functions

Horizontal (across-vector) operations do not abstract portably at fixed
cost, so they live in the architecture library, over the same `simd.*`
types:

| Function | Type | Instruction | Semantics |
| --- | --- | --- | --- |
| `arm64.uaddlv_u8x16` | `(simd.U8x16) -> u32` | `UADDLV` | widening sum of all 16 lanes (max 4080, exact) |
| `arm64.umaxv_u8x16` | `(simd.U8x16) -> u8` | `UMAXV` | maximum lane |
| `arm64.uminv_u8x16` | `(simd.U8x16) -> u8` | `UMINV` | minimum lane |
| `arm64.cnt_u8x16` | `(simd.U8x16) -> simd.U8x16` | `CNT` | per-lane population count |

All four are total, defined on every input, with portable lowerings and
interpreter implementations that must agree (the same three-witness rule as
the scalar catalog in `92-ffi.md` §3).

## 3. Program shape

```oak
contains16: (v: []u8, needle: u8): Bool {
  chunk: simd.U8x16 = simd.load_u8x16(v, u32(0))
  hits: simd.U8x16 = simd.eq_u8x16(chunk, simd.splat_u8x16(needle))
  simd.any_u8x16(hits)
}

sum16: (v: []u8): u32 {
  chunk: simd.U8x16 = simd.load_u8x16(v, u32(0))
  arm64.uaddlv_u8x16(chunk)
}
```

Discipline profiles see vector code as ordinary code: bounded loops over
chunks, assertions on invariants, no hidden allocation anywhere in the
library (vectors are stack values; loads/stores touch only caller-provided
storage).
