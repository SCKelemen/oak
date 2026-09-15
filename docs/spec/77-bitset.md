# Bitsets

Status: normative. The qualified package and reference implementation are
stabilizing. The pre-v1 `BitSetError` and `bitset_*` flat spellings are
direction and will be removed with the bootstrap prelude.

## 1. Scope and representation

The `bitset` package provides bounded logical bitsets over caller-owned byte
storage. It is allocation-free and freestanding.

```oak
import("bitset")

pub Error: type = StorageTooSmall | BitOutOfRange

pub storage_bytes: (bits: u32): u32
pub contains: (storage: []u8, bits: u32, index: u32): Result[Bool, Error]
pub set: (storage: [*]u8, bits: u32, index: u32, value: Bool): Result[Bool, Error]
pub count_ones: (storage: []u8, bits: u32): Result[u32, Error]
```

Logical bit `i` is bit `i % 8` of byte `i / 8`; bit zero is the least
significant bit. `bits` is the logical length. Bytes after
`storage_bytes(bits)` and high bits of the last logical byte are spare storage,
not members of the bitset.

`storage_bytes(bits)` is `ceil(bits / 8)`. It is total for every `u32`: zero
bits require zero bytes and `2^32 - 1` bits require 536,870,912 bytes. The result
is independent of an address or pointer width.

## 2. Reads and mutation

`contains(storage, bits, index)` returns the value of logical bit `index`.
`set(storage, bits, index, value)` writes that logical bit and returns its
previous value. A successful set changes no other logical bit, no spare tail
bit, and no spare byte. Setting a bit to its existing value is permitted.

`count_ones(storage, bits)` returns the number of true logical bits. Its result
is in `0 ..= bits`; spare bits and bytes do not contribute.

The caller supplies and retains all storage. `[]u8` grants read access and
`[*]u8` grants the ordinary exclusive mutable borrow required by `set`. No
operation retains a pointer or borrow after returning or manufactures ownership
from a pointer.

## 3. Failure

Every operation that accesses logical storage first compares the backing length
with `storage_bytes(bits)`.

- Insufficient backing storage returns `Err(StorageTooSmall)` before inspecting
  the requested index, reading a logical byte, or writing anything.
- With sufficient storage, `contains` and `set` return `Err(BitOutOfRange)` when
  `index >= bits`.
- Both failures of `set` are atomic: every backing byte is unchanged.
- `count_ones` has no index and therefore reports only `StorageTooSmall`.

These are recoverable results. An in-contract call does not trap.

## 4. Effects, costs, and portability

`storage_bytes`, `contains`, and `set` perform O(1) work and use O(1) auxiliary
storage. `count_ones` performs O(`bits`) scalar work in ascending index order and
uses O(1) auxiliary storage. No operation allocates, blocks, performs I/O or a
syscall, invokes a callback, uses global mutable state, or requires libc.

Results are deterministic from the visible arguments. The package adds no
synchronization or atomic memory access; callers obey Oak's ordinary borrowing
and memory-model rules. These operations make no constant-time or
secret-independent access-pattern claim.

The package is admitted to the freestanding profile for hosted macOS/Linux,
Oak OS, and STM32-class systems. A word-at-a-time, SIMD, or target-specific
`count_ones` may replace the scalar reference loop only when it preserves the
logical-length and spare-bit rules and its equivalence is checked against the
same laws.

## 5. Evidence and remaining work

- **Specified:** this document.
- **Implemented:** `stdlib/bitset.oak`; `filters` and `bitset_algebra` import the
  qualified package. The flat builder derives the old names from the same
  declarations without exporting generic names from `import(std)`.
- **Tested:** `compiler/e2e_stdlib_bitset_package_test.go` runs the qualified
  API through compiled C and the interpreter, covers size boundaries,
  previous-value results, logical counting, spare-bit preservation, capacity
  precedence, atomic failures, allocation absence, flat agreement, and
  namespace isolation. Existing model-generated flat tests remain in
  `compiler/e2e_stdlib_bits_endian_test.go`.
- **Modeled:** `spec/lean/Oak/Stdlib/BitsetExtracted.lean` is generated from the
  checked Oak source and held by the extraction drift test.
- **Proved:** `spec/lean/Oak/Stdlib/BitsetLaws.lean` proves the zero and maximum
  storage sizes, capacity-first rejection for reads, writes, and counting,
  byte-for-byte preservation on both write failures, and zero-domain counting.
- **Refined:** not yet; the project-wide extractor/compiler boundary remains as
  recorded in `95-extraction.md` and `126-verification-chain.md`.

Universal success-path theorems for read-after-set, preservation of every other
bit, exact logical counting, and extraction-versus-C faithfulness remain open.
Those are the prerequisites for a supported word/SIMD counting realization.
