# Bounded array lists

Status: normative. The qualified allocation-free package and scalar reference
implementation are stabilizing. Allocator-backed growth is not part of this
contract.

## 1. Scope and API

`array_list` manages the initialized prefix of caller-owned contiguous storage.
The cursor is separate value state and retains no pointer.

```oak
import("array_list")

pub Error: type = Full | Empty | OutOfBounds
pub Cursor: type = struct { length: u32 }

pub push[T]: (cursor: [*]Cursor, storage: [*]T, value: T): Result[u32, Error]
pub get[T]: (cursor: [*]Cursor, storage: []T, index: u32): Result[T, Error]
pub set[T]: (cursor: [*]Cursor, storage: [*]T, index: u32, value: T): Result[T, Error]
pub pop[T]: (cursor: [*]Cursor, storage: [*]T): Result[T, Error]
pub insert[T]: (cursor: [*]Cursor, storage: [*]T, index: u32, value: T): Result[u32, Error]
pub remove[T]: (cursor: [*]Cursor, storage: [*]T, index: u32): Result[T, Error]
pub swap_remove[T]: (cursor: [*]Cursor, storage: [*]T, index: u32): Result[T, Error]
pub clear: (cursor: [*]Cursor, capacity: u32): ()
```

The zero value of `Cursor` is an empty list. Every operation validates that the
cursor span has exactly one element and `length <= capacity` before accessing
storage. A cursor must remain paired with the same backing storage or an equal
capacity supplied to `clear`.

## 2. Semantics and failure frames

Live values occupy `storage[0:length]`. `push` appends and returns the inserted
index. `get` copies a value. `set` returns the replaced value. `pop` removes the
last value. `insert` permits `index == length` and shifts the suffix right;
`remove` shifts the suffix left and preserves order. `swap_remove` replaces the
removed position with the last live value and does not preserve order. `clear`
sets length to zero without erasing elements.

`Full`, `Empty`, and `OutOfBounds` are recoverable results. Their conditions are
decided before the first write, so every error preserves cursor and storage
exactly. An invalid cursor invariant is a caller-contract violation and traps.
Elements outside the live prefix remain initialized but stale; removing or
clearing a value does not destroy a resource hidden inside it. This first
surface therefore applies to ordinary copyable values.

## 3. Cost, storage, and portability

`push`, `get`, `set`, `pop`, `swap_remove`, and `clear` take O(1) operations plus
the cost of copying one `T`. Ordered insertion and removal take O(length-index)
element copies. All operations use O(1) auxiliary storage and perform no
allocation, deallocation, I/O, blocking, synchronization, target dispatch, or
callbacks.

The package assumes no heap, libc, pointer width, byte order, unaligned access,
SIMD, threads, or operating system. Its portable Oak body is suitable for
hosted macOS/Linux, Oak OS, and STM32-class freestanding targets. A bulk-move,
SIMD, or target-specific realization must preserve exact results, failure
frames, traps, overlap behavior, and the explicit storage policy.

## 4. Evidence and remaining work

- **Implemented:** `stdlib/array_list.oak`; `stdlib/source.go` mechanically
  derives `ArrayListCursor`, `CollectionError`, and `array_list_*` compatibility
  spellings for `import(std)` from the same implementation.
- **Tested:** the qualified package runs through the C backend and interpreter
  for `u8` and `u32`, covers every error frame and mutation family, namespace
  isolation, flat agreement, invalid-cursor traps, and allocator absence. The
  existing legacy trace compares 100 generated operations at capacities 1, 4,
  and 9 with an independent sequence model.
- **Modeled:** `ArrayListExtracted.lean` is generated from the checked Oak
  source and held by the extraction drift test.
- **Proved:** `ArrayListLaws.lean` proves cursor validation, full/empty/OOB
  failure frames, and clear for arbitrary valid inputs.
- **Refined:** not yet. Successful shift contents, generic parametricity,
  extraction-to-backend correspondence, and target bulk-move refinement remain
  open.

An owning fixed-inline elevation or allocator-backed growable list may be added
as a separate type. It must make capacity, movement, allocation, and failure
policy explicit; this low-level package remains the common engine.
