# Contiguous byte buffers and builders

Status: normative. The qualified allocation-free package and scalar reference
implementation are stabilizing. Borrow-returning observation APIs remain future
work.

## 1. Scope

`buffer` provides two elevations over caller-owned byte storage:

- `Cursor` is the low-level state of a contiguous byte queue;
- `Builder` is a small value that supports fluent, sticky-failure construction.

Neither type owns, allocates, retains, or frees storage. The caller passes the
storage on every operation, so stack, static, arena, runtime-owned, and device
memory policy remains visible.

```oak
import("buffer")

pub Cursor: type = struct { start: u32, end: u32 }
pub Error: type = Full | InsufficientData

pub live_len: (cursor: [*]Cursor, capacity: u32): u32
pub tail_space: (cursor: [*]Cursor, capacity: u32): u32
pub append: (cursor: [*]Cursor, storage: [*]u8, src: []u8): Result[u32, Error]
pub peek_into: (cursor: [*]Cursor, storage: []u8, dst: [*]u8): Result[u32, Error]
pub consume: (cursor: [*]Cursor, capacity: u32, count: u32): Result[u32, Error]
pub read_into: (cursor: [*]Cursor, storage: []u8, dst: [*]u8): Result[u32, Error]
pub compact: (cursor: [*]Cursor, storage: [*]u8): u32
pub reset: (cursor: [*]Cursor): ()
```

## 2. Cursor invariant and queue semantics

A cursor is paired with one backing allocation and satisfies
`0 <= start <= end <= capacity`. The API takes a one-element mutable cursor
span, traps before storage access when its length or invariant is invalid, and
uses subtraction only after establishing the ordering. Live bytes occupy
`[start, end)`.

`append` copies the whole source at `end` and advances `end`, or returns
`Full` with cursor and storage unchanged. It does not compact implicitly;
`tail_space` is contiguous tail capacity, not total reclaimable capacity.

`peek_into` is exact: it fills the complete destination without consuming, or
returns `InsufficientData` without writing. `read_into` performs that exact copy
then consumes only on success. `consume` advances by the exact requested count;
consuming the final live byte canonicalizes the cursor to `(0, 0)`. A rejected
peek/read/consume is atomic.

`compact` moves the live interval to offset zero and returns its length. It
copies forward, which is overlap-safe because the destination begins before the
source. `reset` clears only logical state and does not erase bytes.

Copy operations are O(bytes copied), compact is O(live bytes), and metadata
operations are O(1). Every operation uses O(1) auxiliary storage and performs
no allocation, I/O, blocking, synchronization, target dispatch, or callbacks.

## 3. Value-state builder

```oak
pub Builder: type = struct { length: u32, failed: Bool }
pub builder: (): Builder
pub append_bytes: (state: Builder, storage: [*]u8, src: []u8): Builder
pub append_byte: (state: Builder, storage: [*]u8, value: u8): Builder
pub finish: (state: Builder): Result[u32, Error]
```

The zero value and `builder()` both represent an empty successful prefix. A
successful append returns updated value state. An append that does not fit
writes nothing and returns the same length with `failed = true`; all later
appends are storage-preserving fixed points. `finish` returns the exact prefix
length or `Err(Full)`.

Uniform call syntax provides the high-level form
`buffer.builder().append_byte(storage, value).finish()`. It resolves statically
to the same exported functions, evaluates each receiver once, and introduces no
box, closure, vtable, retained pointer, or intermediate tree. Builder copies are
ordinary value copies; callers must keep a chain paired with the intended
storage. The builder intentionally preserves earlier successful writes rather
than pretending the whole construction is transactional.

## 4. Storage, portability, and concurrency

The caller initializes storage and retains ownership. The package retains no
borrow after return. Mutable storage calls require exclusive access under Oak's
ordinary borrowing rules; this is a sequential queue, not an atomic ring.
Copying a cursor does not create independent ownership of its backing bytes.

The package is freestanding on hosted macOS/Linux, Oak OS, and STM32-class
targets: it assumes no heap, libc, pointer width, byte order, unaligned access,
SIMD, threads, or operating system. A bulk-copy or target-specific realization
must preserve exact results, cursor state, storage frames, traps, failure
atomicity, and the lack of implicit compaction/allocation.

## 5. Evidence and remaining work

- **Implemented:** `stdlib/buffer.oak`; `stdlib/source.go` mechanically derives
  the old `ByteBufferCursor`, `BufferError`, `buffer_*`, `ByteBuilder`, and
  builder-function spellings for `import(std)`.
- **Tested:** the qualified package runs through the C backend and interpreter,
  covers success and every failure frame, compaction, reset, sticky and fluent
  building, namespace isolation, flat agreement, and allocator absence. The
  existing generated trace compares 120 operations at capacities 1, 4, and 9
  with an independent byte-queue model.
- **Modeled:** `BufferExtracted.lean` is generated from the checked Oak package
  and held by the extraction drift test.
- **Proved:** `BufferLaws.lean` proves live/tail arithmetic, atomic full append,
  atomic short peek/consume, canonical reset, sticky builder fixed points, and
  both `finish` outcomes for arbitrary valid inputs.
- **Refined:** not yet. Bulk-copy lowering and extraction-to-backend
  correspondence remain open.

Borrow-returning live views await the region-indexed return surface. A typed
elevation that owns fixed inline storage may be added when it removes repeated
pairing obligations without introducing aggregate-copy surprises.
