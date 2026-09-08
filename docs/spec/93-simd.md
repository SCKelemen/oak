# Portable SIMD and Architecture Vector Instructions

Oak's SIMD story follows the abstract-machine rule of `92-ffi.md` §3, in the
style of Go's portable `simd` package: **one portable vector library with
total, exactly specified lane semantics**, realized by each backend as the
target's vector instructions where they exist and as proven-equivalent
portable scalar code where they do not. Architecture libraries (`arm64`)
additionally expose the instructions that have no portable meaning worth
abstracting (horizontal reductions, lane population counts) as ordinary
typed functions over the same vector types.

A second, deliberately distinct abstraction is reserved for **scalable vector
execution**. Fixed vector values and scalable execution must not be conflated:
a fixed vector's lane count is language semantics; a scalable execution width
is selected by the backend/hardware for one bounded chunk of work.

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

The 128-bit size is a semantic representation contract for these types, **not
a claim about the target's physical vector-register width**. A backend may
use one hardware vector register, part of a wider register, multiple narrower
operations, or scalar code, provided the exact fixed-lane semantics are
preserved.

Signed, float, and wider vectors are reserved for later revisions; the
naming (`I32x4`, `F32x4`, 256-bit `U8x32`) is fixed now so programs and
backends do not fork conventions.

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

On a scalable-vector target such as RISC-V V or AArch64 SVE, fixed vectors
remain fixed semantic values. The backend may use a scalable register to
implement them, but physical VLEN is never observable through `U8x16` or any
other fixed type.

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

## 4. Scalable vector execution

RISC-V V and AArch64 SVE demonstrate that bulk SIMD should not require source
programs to know the physical register width. Oak therefore reserves a
separate scalable execution model rather than extending fixed vector types
with target-dependent lane counts.

The scalable model has these normative design constraints:

1. **Hardware width is not a type property.** The source program supplies a
   remaining element count; the backend chooses a positive active extent not
   greater than that count and its target capacity. The loop advances by the
   returned extent. This is the portable strip-mining model.
2. **The active extent is explicit semantic state.** It is not inferred from
   register contents. Bounds proofs and memory effects apply only to active
   lanes.
3. **Inactive and tail lanes are not Oak values.** Reading, storing, reducing,
   comparing, or otherwise observing a lane outside the active extent is not
   an operation in the scalable API. A backend is therefore free to use
   hardware tail-agnostic/mask-agnostic policies without introducing
   indeterminate Oak values or undefined behavior.
4. **Predicates are logically distinct from data vectors.** The scalable API
   will use a first-class predicate/mask value whose observable domain is the
   active extent. It will not require all-ones integer data vectors merely to
   represent control predicates. Fixed v1 `eq_E -> E` remains unchanged for
   compatibility.
5. **Masked-off lanes do not perform memory effects.** A masked load/store may
   access only active-and-enabled lanes. This rule is semantic and must be
   preserved by every backend.
6. **No implicit vector state crosses ordinary calls.** Physical vector length,
   element-width configuration, restart state, predicate registers, rounding
   mode, and saturation flags are backend machine state. Unless an explicit
   future vector calling convention says otherwise, ordinary Oak calls may
   clobber that state and the compiler must re-establish what it needs.
7. **Scalable values are initially block-local and non-ABI.** They do not live
   in records, globals, stable wire layouts, FFI signatures, or ordinary
   function parameters/returns. This avoids baking one target's vector calling
   convention or VLEN into Oak's stable ABI.
8. **The cost remains bounded by caller-visible work.** One scalable operation
   touches at most the active extent selected for the current chunk; loops over
   a span still carry Oak's ordinary bounded-loop obligations.

A future source surface may expose the strip-mining shape approximately as:

```oak
remaining: u32 = len(input)
offset: u32 = u32(0)
while remaining != u32(0) bounded_by len(input) {
  active: simd.Active = simd.active_u8(remaining)
  chunk: simd.ScalableU8 = simd.load_active_u8(input, offset, active)
  // operations preserve `active`
  simd.store_active_u8(output, offset, chunk, active)
  offset = offset + simd.count(active)
  remaining = remaining - simd.count(active)
}
```

The spelling is non-normative in v1; the semantic constraints above are the
design boundary.

### 4.1 Tail and mask policy

Oak does **not** expose a generic "agnostic value" to source programs. The
hardware distinction between undisturbed and agnostic inactive/tail elements
is a lowering choice whenever those elements are semantically dead. If the
program requires preservation, that preservation must be visible in the Oak
operation (for example by merging a result under a predicate) and the backend
must select an undisturbed or equivalent lowering.

This lets out-of-order RVV/SVE implementations avoid unnecessary preservation
work while preserving Oak's rule that every observable value has exact
semantics.

### 4.2 Fault-only-first and restartable vector memory

RISC-V V's fault-only-first loads are useful for vectorizing bounded scans with
data-dependent termination, but they combine memory access, partial progress,
and fault behavior. Oak must not expose them as an ordinary total load.

A future portable primitive may return both a loaded scalable value and an
explicit completed element count. Its contract must state:

- element 0 fault behavior separately from later-element shortening;
- which memory effects occurred before the returned count;
- that inaccessible elements past the completed count are not semantically
  loaded;
- that `completed` is progress, not merely a fault index: a backend may
  complete fewer elements than requested even without a synchronous fault;
  for a nonzero request it must either trap at element 0 or report positive
  progress;
- that non-idempotent/device/MMIO memory is excluded unless a machine-specific
  contract proves restart/partial-access behavior safe;
- that partial progress is represented as a result, never hidden mutable vector
  restart state;
- that privileged fault-first access is authority-sensitive because completion
  length can reveal where addressability changes; callers must not gain a
  mapping-probe capability merely by using a SIMD primitive.

Architecture-specific fault-first instructions may be exposed earlier through
a target library if their machine contract is explicit.

## 5. Cross-target verification obligations

Adding a scalable backend does not weaken the three-witness rule. Verification
must cover at least:

- the same fixed-vector program under portable scalar, AArch64 NEON, and a
  scalable backend;
- multiple emulated hardware vector lengths for the same scalable program;
- final partial chunks of every size from zero through the target maximum;
- masked operations with every-active, none-active, and mixed predicates;
- proof/tests that inactive/tail lanes cannot affect reductions, stores,
  comparisons, control flow, or returned Oak values;
- call boundaries that clobber target vector configuration and require correct
  re-establishment;
- fault-first behavior separately from ordinary total vector loads, including
  legal short completion without a synchronous fault and zero-progress
  rejection for nonzero requests.

A scalable implementation is not considered portable merely because it runs on
one VLEN. The same Oak source must retain its semantics across every supported
hardware vector length.
