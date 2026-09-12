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
| `simd.F32x4` | 4 | `f32` |
| `simd.F64x2` | 2 | `f64` |

A vector is an ordinary 16-byte **value**: copyable, stack-resident, no
borrow interaction, no implicit conversion between vector types or to
scalars. Lane order is index order; lane `0` is the first element loaded
from memory (memory order matches view element order, independent of host
endianness at the semantic level).

Signed and wider vectors are reserved for later revisions; the naming
(`I32x4`, 256-bit `U8x32`) is fixed now so programs and backends do not fork
conventions. The floating-point vectors `F32x4` and `F64x2` are specified
with the floating-point types themselves (`20-types.md` §11.3.7) and
implemented: lane-wise `add sub mul div fma min max sqrt neg abs` under the
fixed IEEE semantics of §11.3.3, lane `extract` and `insert`, and a
horizontal `reduce_add` whose pairwise-tree grouping is its semantics
(§1.2a below).

### 1.2 Operations

For each vector type `E` with lane type `uN` and lane count `L` (spelled
with its type suffix, e.g. `simd.add_u8x16`):

| Function | Type | Semantics |
| --- | --- | --- |
| `simd.splat_E` | `(uN) -> E` | every lane is the operand |
| `simd.load_E` | `([]uN, u32) -> E` | lanes `v[off] .. v[off+L-1]`; **traps** unless `off + L ≤ len(v)` — the check is elided where an extent fact proves it (`50-borrowing.md`, vector access) |
| `simd.store_E` | `([*]uN, u32, E) -> ()` | stores the `L` lanes; **traps** unless `off + L ≤ len(s)` — elided under a proving fact likewise |
| `simd.add_E` / `simd.sub_E` | `(E, E) -> E` | lane-wise, wrapping mod `2^N` |
| `simd.and_E` / `simd.or_E` / `simd.xor_E` | `(E, E) -> E` | lane-wise bitwise |
| `simd.min_E` / `simd.max_E` | `(E, E) -> E` | lane-wise unsigned |
| `simd.eq_E` | `(E, E) -> E` | mask: lane is all-ones where equal, zero where not |
| `simd.any_E` | `(E) -> Bool` | true iff **some** lane is nonzero |
| `simd.all_E` | `(E) -> Bool` | true iff **every** lane is nonzero |
| `simd.subs_E` | `(E, E) -> E` | lane-wise saturating subtract: `x - y` when `y ≤ x`, else `0` |
| `simd.shr_E` | `(E, u32) -> E` | lane-wise logical shift right by the count; a count reaching the lane width **traps** (the scalar shift rule) |
| `simd.tbl_u8x16` | `(U8x16, U8x16) -> U8x16` | byte-table lookup: lane `i` is `table[idx[i]]` when `idx[i] < 16`, else `0` (NEON `tbl`, and `pshufb`'s high-bit rule) |
| `simd.prev_u8x16` | `(U8x16, U8x16, u32) -> U8x16` | the sixteen bytes ending `n` before the end of `prev ++ cur`: lane `i` is `prev[16-n+i]` for `i < n`, `cur[i-n]` otherwise; `n > 16` **traps** |
| `simd.movemask_E` | `(E) -> u32` | one bit per lane: bit `i` is the top bit of lane `i`, every other bit zero. Over an `eq` mask this is the lane mask as a scalar |
| `simd.ctz_u32` / `simd.ctz_u64` | `(uN) -> uN` | trailing zeros; `ctz(0)` is the width |
| `simd.popcount_u32` / `simd.popcount_u64` | `(uN) -> uN` | the number of set bits |

Every operation is **total** — no lane produces undefined behavior for any
input — and loads/stores carry the same never-UB obligation as scalar
view/span access (`50-borrowing`): out-of-range offsets trap. Offsets are
in **elements**, not bytes. Unaligned element access is legal; the backend
is responsible for unaligned-safe lowering.

`eq` masks compose with the bitwise operations and reduce with `any`/`all`:
`simd.any_u8x16(simd.eq_u8x16(chunk, simd.splat_u8x16(needle)))` is the
canonical byte-search kernel, and its law — the reduction is true exactly
when some lane matches — is proven in `Oak.Simd`.

The last four are the byte-classification vocabulary (added 2026-09-12 for
the UTF-8 validator of §1.5): a table lookup indexed by nibbles, the two
nibble extractions (`shr` by four and `and` with fifteen), a saturating
subtraction that turns "at or above a threshold" into a nonzero lane, and
the shift that lets a block see the bytes before it. `Oak.Simd` states each
lane by lane (`subSat_lane`, `subSat_zero_iff`, `shr_lane`,
`tbl_lane_in_range`, `tbl_lane_out_of_range`, `prev_lane_from_prev`,
`prev_lane_from_cur`, `prev_zero`); `compiler/e2e_simd_bytes_test.go` checks
the interpreter, the NEON lowering, and the portable loop agree, and that
the out-of-range counts trap.

The final three rows are the **mask vocabulary** (added 2026-09-12 for
structural indexing in the simdjson shape): `movemask` turns a lane mask
into a scalar, `ctz` walks its set bits, and `popcount` bounds the walk —

```oak
m: u32 = simd.movemask_u8x16(simd.eq_u8x16(chunk, simd.splat_u8x16(quote)))
while m != u32(0) {
  i: u32 = simd.ctz_u32(m)     // the next matching lane
  m = m & (m - u32(1))          // clear it
}
```

runs exactly `popcount(m)` times. All three are total: `ctz` of zero is
the width, as `RBIT` then `CLZ` gives on AArch64, and `popcount` is `CNT`
then `ADDV` — the same instructions as `arm64.cnt32`/`arm64.cnt64`
(`92-ffi.md` §3.2), of which `simd.popcount_u32/u64` is the portable
spelling; the two share `Oak.Intrinsics.popcount`. `movemask` is not one instruction on NEON, and the cost is
stated so the emulation is no surprise: `U8x16` is a test against the top
bit, an `and` with a bit table, and three pairwise adds; `U16x8` and
`U32x4` a test, an `and`, and one horizontal add; `U64x2` two lane
extractions. The portable semantics are the specification; on a target
with `pmovmskb` the lowering is that instruction. `Oak.Simd` states the
laws (`movemask_lt`: the mask is below `2^lanes`; `movemask_bit_zero`;
`movemask_eq_zero_iff`: zero exactly when no lane has its top bit set) and
`Oak.Intrinsics` the scalar ones (`ctz_le_width`, `ctz_zero`,
`ctz_lt_of_mem_true`, `popcount_le_width`, `popcount_zero`,
`popcount_eq_zero_iff`); `compiler/e2e_simd_bytes_test.go` runs the three
witnesses over masks with every shape and the zero and all-ones words.

### 1.2a Floating-point vectors

For `E` in `F32x4`, `F64x2` with lane type `fN` (suffix `f32x4`, `f64x2`),
every lane obeys the scalar rules of `20-types.md` §11.3.3 and §11.3.5:

| Function | Type | Semantics |
| --- | --- | --- |
| `simd.splat_E` / `simd.load_E` / `simd.store_E` | as for the integer vectors | loads and stores **trap** out of range |
| `simd.add_E` / `sub_E` / `mul_E` / `div_E` | `(E, E) -> E` | lane-wise, one rounding each, never contracted |
| `simd.fma_E` | `(E, E, E) -> E` | lane-wise `a * b + c` in one rounding |
| `simd.min_E` / `simd.max_E` | `(E, E) -> E` | IEEE 754-2019 `minimum`/`maximum`: a NaN operand yields NaN, `-0.0` orders below `+0.0` |
| `simd.sqrt_E` / `neg_E` / `abs_E` | `(E) -> E` | lane-wise; `neg` and `abs` are sign-bit operations |
| `simd.extract_E` | `(E, u32) -> fN` | the lane; **traps** when the index is not below the lane count |
| `simd.insert_E` | `(E, u32, fN) -> E` | the vector with one lane replaced; same trap |
| `simd.reduce_add_E` | `(E) -> fN` | `(l0 + l1) + (l2 + l3)` for four lanes, `l0 + l1` for two: the grouping is the semantics (`55-parallelism.md` §4) |

There is no `eq`, `any`, or `all` over float vectors in v1: lane comparison
yields a mask over an integer vector, and that operation is reserved with the
comparison masks of a later revision. The lowering uses the NEON
instructions where the target has them (`vminq`/`vmaxq` already have the
2019 semantics, `vfmaq` is one rounding) and the float preamble's helpers in
the portable lane loop; `reduce_add` is emitted as the explicit pairwise
expression in both, so the grouping is identical on every target. The
interpreter holds lanes as IEEE bit patterns and matches bit for bit
(`compiler/e2e_float_simd_test.go`, compiled with and without
`OAK_PORTABLE_INTRINSICS`).

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

**The RISC-V Vector realization (landed; dbs ask 7, first increment).**
Every helper carries a third branch beside NEON and the lane loop, selected
by the preprocessor when the target is RISC-V with the V extension
(`-target linux/riscv64 -cpu generic_rv64+m+v`, or `+v` on a freestanding
processor; `__riscv_vector`): `<riscv_vector.h>` LMUL=1 intrinsics with the
vector length fixed to the lane count (`vle`/`vse`, `vmv.v.x`, `vadd`,
`vsub`, `vssubu`, `vand`/`vor`/`vxor`, `vminu`/`vmaxu`, `vmseq` merged to
all-ones lanes for `eq`, `vsrl.vx` for `shr`, `vrgather` under an explicit
index-below-16 mask for `tbl` so the out-of-range rule holds on every VLEN,
`vslidedown` then `vslideup` for `prev`, `vfadd`/`vfsub`/`vfmul`/`vfdiv`,
`vfsqrt`/`vfneg`/`vfabs`, `vfmacc` for `fma`). Fixed 128-bit vectors run
unchanged on every VLEN ≥ 128. What keeps the portable code on every
target, by design: the reductions `any`/`all`/`movemask`/`reduce_add`
(the pairwise order is the semantics), `extract`/`insert`, and floating
`min`/`max` — RVV's `vfmin`/`vfmax` are IEEE `minimumNumber`/
`maximumNumber` (a NaN operand suppressed, `-0.0` equal to `+0.0`), not
the catalog's 754-2019 `minimum`/`maximum`. The choice is static: no
runtime dispatch, no hidden state, one lane-array representation for every
realization. On an SVE processor the fixed vectors stay NEON (the
`Z` registers' low 128 bits are the `V` registers); SVE enters only through
the scalable API of §4.

### 1.5 A byte-classification kernel: the UTF-8 validator

`stdlib/utf8.oak` (`utf8 := import("utf8")`, `utf8.valid: ([]u8) -> Bool`)
is the lookup-table validator of Keiser and Lemire, as shipped in simdjson
and simdutf, written in Oak over `U8x16`: three 16-entry tables indexed by
the previous byte's two nibbles and the current byte's high nibble classify
every byte pair in one `tbl` each and one `and`; a saturating subtraction
against the bytes two and three back permits a continuation after a
continuation exactly under a three- or four-byte lead; a block that ends
inside a sequence carries an `incomplete` mask into the next block; the
tail is zero-padded, since zero is ASCII and cannot complete anything. The
stream is taken sixty-four bytes at a step — four loads, one reduction to
decide whether the step is pure ASCII, and the classification only when
it is not — under the wrap-free guard
`while len(bytes) >= u32(64) && off <= len(bytes) - u32(64)`, so every
load is proven in range and emitted without its check (`50-borrowing.md`,
vector access); the continuation permission is read off the high bit of
`subs(prev2, 0x60) | subs(prev3, 0x70)` with no comparison. The measured
result (`benchmarks/state-machines/cross/`) is 13.1 GB/s on Apple arm64
beside simdutf's 13.3 and simdjson's 13.3; a scalar Table 3-7
transliteration written in Oak runs at 0.37, Go's speed.

The proof runs from the tables to the program. `Oak.Utf8Lookup` decides,
by bit-blasting over all 65,536 byte pairs, that the tables' low seven
bits are nonzero exactly on the pairs Unicode Table 3-7 forbids on their
own (`sc_error`), that the top bit is set exactly when both bytes are
continuations (`sc_two_conts`), and that the incomplete maxima and the
permission thresholds are the ones the algorithm needs. `Oak.Utf8Stream`
states the lane function exactly as the source spells it and proves that,
composed down the stream from the zero context, every lane is zero and
the stream ends at a boundary **iff** the bytes are valid under
`Oak.Utf8Validity.Valid` (`scan_valid`; each sequence class is one
bit-blasted fact, the induction is over the sequences). `Oak.Utf8Flat`
restates it by position, and `Oak.Utf8Blocks` is the program — blocks of
sixteen lanes shifted against the block before them (`checkBlock_lane`:
lane `i` of block `b` is stream position `16 b + i`), the sixty-four-byte
step, the ASCII shortcut (`ascii_block`: for a block with no high bit, the
error lanes are nonzero exactly when the previous block's `incomplete`
lanes are), the zero-padded tail — proved to accept exactly the valid
streams (`program_valid`). The differential test
(`compiler/e2e_stdlib_utf8_test.go`) checks the emitted C under both
lowerings against a scalar Table 3-7 transliteration written in Oak over
edge cases and three thousand random corrupted inputs. On this proof the
builtin `is_valid_utf8` lowers to `utf8.valid` in every module build
(`70-strings.md` §4): a program that reaches it, or `str_from_utf8`, loads
`utf8` implicitly and the runtime helper is a call to the compiled
validator. A bare source build, which has no packages, keeps the scalar C
transliteration of `Oak.Utf8Validity`.

`utf8.locate` is the positioned form (`70-strings.md` §4a): the same
steps, classified one at a time, and the first step whose error lanes — or
carried `incomplete` mask — are nonzero hands over to
`strings.utf8_first_error_at` from a sequence boundary found by stepping
three bytes back and advancing over continuation bytes; everything before
the step passed the vector classification, so the failing lead is within
those three bytes. Reject fast, locate slow, as simdutf's `_with_errors`
variants do; the differential test checks `locate` against the library's
scalar decoder and against a third scalar oracle written in the test, on
every edge case (including a lead left open at byte 63 before an ASCII
step, and a stray continuation at byte 64) and the random corrupted inputs.

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

**Landed subset (dbs ask 7, second increment).** The shape above is now the
surface, for `u8` and `u32` lanes: `simd.Active`, `simd.ScalableU8`,
`simd.ScalableU32`; `simd.active_u8(remaining)` / `active_u32(remaining)`
choose an extent no wider than the remaining count nor the realization's
capacity, `simd.count(active)` reads it; `splat_active_E(x, a)`,
`load_active_E(v, off, a)` (traps unless `off + count ≤ len(v)`),
`store_active_E(s, off, x, a)`, the lane-wise `add sub subs and or xor min
max eq _active_E(x, y, a)` and `shr_active_E(x, n, a)`, `any_active_E` and
`all_active_E`, and `reduce_add_active_u32` (the wrapping sum over the
active lanes). Every operation takes the extent it applies to; lanes
outside it are never read. The types are **block-local** (item 7,
`OAK-S0401`): a local or an expression, never a record field, a global, a
parameter, a result, or an array element — which is what lets a backend
hold them in sizeless registers.

Realizations: the portable one is a 16-byte vector and a `u32` extent
(capacity 16 lanes for `u8`, 4 for `u32`); RISC-V Vector holds
`vuint8m1_t`/`vuint32m1_t` block-locals with the extent from `vsetvl`
(capacity `VLEN/8` and `VLEN/32` lanes); **AArch64 SVE (third increment)**
holds `svuint8_t`/`svuint32_t` block-locals with the extent as a lane
count, capacity `svcntb()`/`svcntw()`, and every operation under the
predicate `whilelt(0, count)` rebuilt from the extent — zeroing forms for
the lane-wise operations, `ld1`/`st1` under the predicate, `cmpeq` widened
to all-ones lanes for `eq`, `ptest` for `any`/`all`, `addv` for the sum,
and the unpredicated `uqsub` for `subs` (inactive lanes are never read).
It is selected by an SVE processor (`-target linux/arm64 -cpu
neoverse_v2`, or `generic+sve` freestanding; `__ARM_FEATURE_SVE`); the
fixed 128-bit vectors keep their NEON realization on the same processor.
The interpreter uses the portable
capacity, lowered on request so a test can stress a program at extents of
one, three, or five lanes. **Extent independence** is the semantics
(`Oak.Simd.chunked_map_eq`, `chunked_sum_eq`, `chunked_any_eq`,
`chunked_all_eq`): a lane-wise map over any chunking is the map of the
whole, the wrapping sum of chunk sums is the whole's, and `any`/`all`
folded with or/and across chunks are the whole's. Two things a program
must therefore do: fold per-chunk observations (`found = found ||
any(...)`), since the number of chunks depends on the extent
(`chunk_count_depends_on_extent`); and bound the request when staging
lanes into fixed storage (`active_u8(remaining < 16 ? remaining | 16)`),
since the backend may otherwise choose a wider extent — at VLEN 256 an
unbounded request is 32 lanes. `compiler/e2e_scalable_test.go` is the
worked program, over every input length from zero to forty.

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

Discharged for the fixed vectors under the RVV realization
(`compiler/e2e_rvv_test.go`): the byte-classification and floating-point
programs of the NEON and portable witnesses run under `qemu-system-riscv64`
with V at VLEN 128 and 256 and print the interpreter's checksum — the same
program under portable scalar, NEON, and a scalable backend, at two
emulated hardware vector lengths. Discharged for the scalable API's landed
subset (`compiler/e2e_scalable_test.go`): final partial chunks of every
size from zero through the maximum (inputs of every length 0..40), the
same program at extents 1, 3, 5, and 16 in the interpreter, portable C,
RVV at VLEN 128 and 256 (extents 16 and 32), and SVE at 128, 256, and 512
bits (extents 16, 32, and 64, `compiler/e2e_sve_test.go` under
`qemu-system-aarch64 -cpu max,sve-max-vq=1|2|4`), and tail lanes unable to
affect stores, reductions, or returned values — every operation takes its
extent, and Lean states the independence. Still open: predicated
(masked) operations, fault-first loads, and the call-boundary
re-establishment of vector state (no scalable value crosses a call by the
locality rule; the backend's `vsetvl` is re-issued per chunk).
