# Bytes

Status: normative. The qualified package and its reference implementation are
stabilizing. The pre-v1 flat compatibility names are direction and will be
removed with the flat bootstrap surface.

## 1. Scope

The `bytes` package provides allocation-free operations over byte views and
caller-owned mutable spans. It is a freestanding pure-foundation package: it
requires no allocator, operating system, runtime, global state, or target
feature.

This foundation surface is deliberately concrete:

```oak
import("bytes")

pub CopyError: type = | DestinationTooSmall
pub RangeError: type = | OutOfBounds

pub range_fits: (length: u32, offset: u32, width: u32): Bool
pub copy_into: (dst: [*]u8, src: []u8): Result[u32, CopyError]
pub equal: (left: []u8, right: []u8): Bool
pub find: (src: []u8, needle: u8): Option[u32]
pub fill: (dst: [*]u8, value: u8): ()
pub copy_at: (dst: [*]u8, offset: u32, src: []u8): Result[u32, RangeError]
pub move_within: (storage: [*]u8, dst: u32, src: u32, count: u32): Result[u32, RangeError]
pub compare: (left: []u8, right: []u8): i32
```

`Option` is the current implementation spelling of the v1 `Optional` type
specified by `75-standard-library.md`. The package will migrate when the
canonical type does.

## 2. `copy_into`

`copy_into(dst, src)` copies the complete logical source into the prefix of
`dst`.

- When `len(dst) >= len(src)`, it writes `src[i]` to `dst[i]` for every
  `0 <= i < len(src)`, leaves the remaining destination suffix unchanged, and
  returns `Ok(len(src))`.
- When `len(dst) < len(src)`, it returns `Err(DestinationTooSmall)` before any
  write. The destination is byte-for-byte unchanged.
- An empty source succeeds with `Ok(0)` and performs no write.

The mutable destination and immutable source are ordinary checked borrows. They
must satisfy Oak's provenance, lifetime, initialization, bounds, and exclusivity
rules. `copy_into` is not an overlapping-memory move primitive; a caller needing
overlap semantics must use an API whose contract states an overlap direction or
temporary-storage rule.

Work is O(`len(src)`) after the constant-time capacity check. The operation uses
O(1) auxiliary storage, performs no allocation, and makes one read and one write
per copied byte. It does not trap for an in-contract call.

## 3. `equal`

`equal(left, right)` returns true exactly when the views have the same length
and the byte at every index is equal. A length mismatch returns false.

The reference implementation does O(1) work for a length mismatch and
O(`len(left)`) work for equal lengths, with O(1) auxiliary storage and no
allocation. This is ordinary sequence equality. It makes no constant-time,
secret-independent timing, or other side-channel claim; cryptographic callers
must use a separately specified operation.

## 4. `find`

`find(src, needle)` returns `Some(i)` for the least index `i` at which
`src[i] == needle`, or `None` when no such index exists. Empty input returns
`None`.

It reads at most `len(src)` bytes in ascending index order, performs
O(`len(src)`) work in the reference implementation, uses O(1) auxiliary
storage, and does not allocate. It makes no secret-independent timing claim.

## 5. Ranges, initialization, movement, and ordering

`range_fits(length, offset, width)` is true exactly when `offset <= length` and
`width <= length - offset`. It checks the ordering before subtraction and never
forms `offset + width`, so hostile `u32` offsets cannot wrap the validation. A
zero-width range fits at the end but not beyond it.

`fill(dst, value)` writes `value` to every byte. `copy_at(dst, offset, src)`
copies the complete source at that offset and returns `Ok(len(src))`; an invalid
range returns `Err(OutOfBounds)` before any write. Both are O(the number of
written bytes), O(1) auxiliary storage, and allocation-free.

`move_within(storage, dst, src, count)` is the overlapping move primitive. Its
single exclusive span makes aliasing explicit. It copies backward when the
destination begins above the source and forward otherwise, with memmove
semantics. Either complete range being invalid returns `Err(OutOfBounds)` with
the entire storage unchanged. Success returns `Ok(count)`. Work is O(count),
auxiliary storage O(1), with no allocation.

`compare(left, right)` returns -1, 0, or 1 according to unsigned-byte
lexicographic order; a shorter equal prefix sorts first. It performs O(minimum
length) byte comparisons and uses O(1) auxiliary storage. No constant-time
claim is made.

## 6. Common contract

All operations are deterministic functions of the bytes and logical
lengths visible through their arguments. They perform no I/O, blocking,
syscalls, synchronization, target dispatch, or transitive callbacks. Mutation
is limited to the destination ranges named by `copy_into`, `fill`, `copy_at`,
and `move_within`.

The caller supplies and retains all storage. No operation retains a pointer or
borrow after returning. Concurrent access is permitted only when the ordinary
Oak borrowing and memory-model rules permit it; this package adds no atomicity
or synchronization. Logical lengths are `u32`, so every accessed index is
representable on 32- and 64-bit targets and no pointer-width assumption enters
the public result.

The package belongs to the freestanding profile and must build for hosted
macOS/Linux, Oak OS, and STM32-class targets without a heap or libc. A future
SIMD or target-specific realization must preserve these exact results, failure
atomicity, storage effects, and side-channel non-claim. Such a realization is
admitted only after its semantic equivalence is mechanically checked or its
remaining correspondence is explicitly recorded.

## 7. Evidence and remaining work

- **Specified:** this document.
- **Implemented:** `stdlib/bytes.oak`; the legacy flat builder derives the old
  `bytes_*` spellings from the same declarations without exporting them from
  the qualified package.
- **Tested:** `compiler/e2e_stdlib_bytes_package_test.go` executes the qualified
  package through both the C backend and interpreter; checks copying, fill,
  hostile range inputs, atomic failures, both overlap directions, lexicographic
  comparison, equality, first-match search, and flat-surface agreement; and
  rejects allocator calls and unrelated higher-level package code.
- **Modeled:** `spec/lean/Oak/Stdlib/BytesExtracted.lean` is generated from the
  checked Oak package and held by the extraction drift test.
- **Proved:** `spec/lean/Oak/Stdlib/BytesLaws.lean` proves short-copy rejection
  and destination preservation for arbitrary arrays and fuel, unequal-length
  rejection, empty search/copy/compare, non-wrapping range edges, and atomic
  rejected offset copy/move directly over the extraction.
- **Refined:** not yet. The extractor/compiler correspondence remains the
  project-wide boundary described by `95-extraction.md` and
  `126-verification-chain.md`.

Full extracted semantic theorems for successful copying/movement,
equal-length equality, lexicographic order, and first-index search remain open,
as does executable extraction-versus-C faithfulness coverage. Optimized
implementations and benchmarks follow those laws rather than changing the API.
