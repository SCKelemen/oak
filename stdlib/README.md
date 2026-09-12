# Oak standard library, bootstrap implementation

`import(std)` loads the embedded Oak source in `stdlib/std.oak` through the
normal compiler pipeline. The library executes as generated C; its functions
are not Go runtime shims. Use `go run . program.oak` to emit C, then compile
that C with `cc -std=c99 -O2 program.c -o program`.

The bootstrap module has unqualified exports. Repeated imports are idempotent;
conflicting declarations, aliases and unknown imports are rejected. A general
package loader and qualified module names remain future work. The interactive
REPL currently uses its older pipeline and does not load this module.

## Values and generic functions

`Option[T]`, `Result[T,E]`, and `Overflow` have canonical declarations within a
compilation using `import(std)`. Checked integer conversions use these declarations.
`option_or[T](item, fallback)` returns the payload or the supplied fallback.
Its fallback is evaluated eagerly, as an ordinary function argument.

Explicit calls such as `identity[u32](x)` and `ring_push[u8](cursor, data, x)`
specialize first-order unconstrained functions. Each concrete signature and body
passes type checking, borrow checking and discipline analysis. Specializations
use direct calls and inline values, with no boxes, vtables or allocation.
The compiler also infers type arguments when call arguments determine them.

The initial argument set is fixed-width integers, Bool and concrete named types.
Const parameters on functions, composite type arguments, generic methods,
and first-class generic function values are not implemented.
Constrained functions retain the existing type-checking path; unsupported generic
bodies are rejected before C emission. Programs are limited to 256 specializations.
Unused unconstrained templates are not emitted or universally body-checked.

## Ring over caller-owned storage

Create an initialized element array and a zero-initialized `[1]RingCursor`, then
borrow each with `span`. Capacity is the storage span's length and must be nonzero.
Keep that cursor paired with that storage for its active lifetime. All operations
require exclusive access; this is a sequential ring, not a concurrent SPSC queue.

```oak
import(std)

main: (): i32 {
  data: [8]u8
  state: [1]RingCursor
  storage: [*]u8 = span(&data)
  cursor: [*]RingCursor = span(&state)
  inserted: RingPush = ring_push[u8](cursor, storage, u8(42))
  item: Option[u8] = ring_pop[u8](cursor, storage)
  i32(option_or[u8](item, u8(0)))
}
```

| Operation | Contract |
| --- | --- |
| `ring_push[T]` | `Inserted` appends; `Full` leaves cursor and storage unchanged |
| `ring_pop[T]` | `Some(T)` removes the oldest element; `None` leaves an empty ring unchanged |
| `ring_check` | Checks cursor span length, nonzero capacity, head range and occupancy |

Push and pop do O(1) bookkeeping plus one element copy; storage costs O(capacity).
No operation grows or allocates. Index wraparound avoids overflowing `head+count`.
The cursor has explicit value semantics: copying it does not transfer ownership,
create independent storage, or duplicate a resource capability. This initial API
is for initialized copyable values; it does not enforce unique resources,
destruction or cursor/storage pairing through typestate.

A future owning `Ring[T,N]` wrapper can bind storage and cursor once borrowing of
aggregate storage is fully supported. The current API exposes both borrows rather
than accidentally passing a whole fixed-size ring by value.

## Reductions (`import("reduce")`)

Reductions whose grouping is a language fact (`docs/spec/55-parallelism.md`
§4; `Oak.Reduce` in Lean).

| Function | Semantics |
| --- | --- |
| `tree[T](xs: []T, zero: T, f: (T, T) -> T)` | The balanced binary-counter tree: four elements give `f(f(x0, x1), f(x2, x3))`, the `simd.reduce_add` grouping; an empty view yields `zero`, which takes no other part. Identical on every backend, no associativity assumed. O(n) work, one 64-entry stack. |
| `left[T](xs: []T, zero: T, f: (T, T) -> T)` | The sequential left fold `f(f(zero, x0), x1) ...`. |

When `f` is an operator declaring `laws { associative }` the two agree on
non-empty input (`Oak.Reduce.tree_assoc`).

## Bytes

| Function | Result and work |
| --- | --- |
| `bytes_copy_into(dst, src)` | `Result[u32,CopyError]`; copies all bytes in O(length), or returns `DestinationTooSmall` before any write |
| `bytes_equal(left, right)` | Bool; O(length) when lengths agree; not a cryptographic constant-time comparison |
| `bytes_find(src, needle)` | `Option[u32]` containing the first matching index; O(length) |

Byte functions allocate nothing. Copy requires the normal nonconflicting
source/destination borrows; it is not an overlapping-memory move primitive.

## Bounded bitsets

Bitsets use caller-owned bytes, with bit zero in the least significant bit of
byte zero. Pass the logical bit count on each call; it may be zero and need not
fill the backing storage. `bitset_storage_bytes(bits)` computes the required
byte count without overflow, including for the maximum u32 bit count.

| Function | Contract |
| --- | --- |
| `bitset_contains(storage, bits, index)` | `Result[Bool,BitSetError]`; reads one logical bit in O(1) |
| `bitset_set(storage, bits, index, value)` | `Result[Bool,BitSetError]`; returns the previous bit and updates it in O(1) |
| `bitset_count(storage, bits)` | `Result[u32,BitSetError]`; counts logical set bits in O(bits) |

Read operations take `[]u8`; set takes `[*]u8`. Insufficient backing storage
returns `StorageTooSmall` before index validation; an index outside the logical
range returns `BitOutOfRange`. Errors do not mutate storage. Set preserves every
other bit, including unused tail bits and spare bytes. Count ignores those bits.
Storage must be initialized; use zero-initialized arrays for an empty set.
These are sequential operations and do not implement atomic bitmap allocation.

## Explicit endian encoding

`bytes_read_u16_le`, `bytes_read_u32_le`, and `bytes_read_u64_le` decode little-endian
integers; replace `_le` with `_be` for big-endian. They accept `(src: []u8,
offset: u32)` and return `Result[u16|u32|u64,EndianError]` with the corresponding
concrete integer type.

The matching `bytes_write_u16_le` / `_u32_le` / `_u64_le` functions (and `_be`
variants) accept `(dst: [*]u8, offset: u32, value)` and return
`Result[u32,EndianError]`: success reports the number of bytes written, not the
next offset. All accesses are byte-oriented, independent of host endianness,
with no alignment requirement beyond byte storage and no allocation.

Every function checks that its entire range fits before indexing or writing.
`BufferTooSmall` covers both an invalid offset and an incomplete integer; failed
writes leave all bytes unchanged. Range checks subtract only after validating
the offset, so even `u32(4294967295)` fails safely. Bytes outside successful
writes remain unchanged. These operations encode integers only; they do not
provide a record format, checksum, persistence ordering, or transaction protocol.

## Byte ranges and contiguous buffers

`bytes_fill(dst, value)` initializes every byte in a mutable span.
`bytes_copy_at(dst, offset, src)` copies the whole source at an explicit offset.
`bytes_move_within(storage, dst, src, count)` moves bytes within one exclusive
span, handling both overlap directions. The latter two return
`Result[u32,ByteRangeError]`; `OutOfBounds` leaves all bytes unchanged. A zero
count permits offsets at the end, but not beyond it. `bytes_compare(left, right)`
returns -1, 0, or 1 in unsigned-byte lexicographic order, with shorter equal
prefixes first. None of these functions allocates.

`ByteBufferCursor` tracks a contiguous live range `[start, end)` in caller-owned
storage. Start with a zero-initialized `[1]ByteBufferCursor` and initialized byte
array. Keep the cursor paired with the same storage; copying it does not create
independent storage. These APIs require exclusive access to the cursor and are
sequential. Corrupted cursors trap before operations access storage.

| Function | Behavior |
| --- | --- |
| `buffer_len(cursor, capacity)` | Number of live bytes |
| `buffer_tail_space(cursor, capacity)` | Available contiguous append space |
| `buffer_append(cursor, storage, src)` | Appends all source bytes or returns `Full`, unchanged |
| `buffer_peek_into(cursor, storage, dst)` | Fills the whole destination without consuming, or returns `InsufficientData`, unchanged |
| `buffer_read_into(cursor, storage, dst)` | Exact peek followed by consume on success |
| `buffer_consume(cursor, capacity, count)` | Advances start, or returns `InsufficientData`, unchanged |
| `buffer_compact(cursor, storage)` | Moves live bytes to offset zero; returns their count |
| `buffer_reset(cursor)` | Clears offsets without erasing storage |

Append, peek, read and consume return `Result[u32,BufferError]` with the byte
count on success. Supply the actual backing capacity to metadata-only operations.
Consuming the last live byte resets both offsets. Append never compacts implicitly;
call compact to reclaim a consumed prefix. Append/read/peek cost O(copied bytes),
compact costs O(live bytes), and metadata operations cost O(1). Storage passed to
append/compact is `[*]u8`; peek/read takes `[]u8` plus a separate mutable destination.
Use lexical scopes to release a write borrow before creating a read view.

Returning borrowed slices is not yet supported by Oak's borrow checker, so these
read APIs copy into caller-provided storage. There is no owning buffer object,
automatic growth, allocator, zero-copy returned view, or implicit byte erasure.

## Fluent byte builder

```oak
import(std)

main: (): i32 {
  data: [4]u8
  storage: [*]u8 = span(&data)
  built: ByteBuilder = byte_builder().
    append_byte(storage, u8(10)).
    append_byte(storage, u8(32))
  result: Result[u32, BufferError] = built.finish_bytes()
  count: u32 = result ? | .Ok(n) => n | .Err(e) => u32(0)
  assert(count == u32(2))
  i32(storage[0]) + i32(storage[1])
}
```

`ByteBuilder` is a small value record containing `length` and `failed`. The builder
owns no storage and holds no borrow. Keep the same storage paired with a chain.
`append_bytes(builder, storage, src)` and `append_byte(builder, storage, value)`
return updated state; `finish_bytes(builder)` returns the length or `Full`.
An append that does not fit writes nothing, preserves the successful prefix,
and sets a sticky failure: later appends write nothing. Earlier successful writes
are not rolled back. Reset by constructing a new builder; this does not erase bytes.
Copies of builder state alias the same caller-selected storage and are not snapshots.

With `import(std)`, the three fluent spellings `.append_bytes(...)`,
`.append_byte(...)`, and `.finish_bytes()` expand into those ordinary functions,
with the receiver supplied exactly once as the first argument. The usual type,
borrow and discipline checks run on the expanded calls. This bootstrap sugar is
limited to these three exports; it is not general method dispatch or generic
method inference. Free-function spelling remains available. For multiline chains,
keep the dot at the end of the preceding line: a leading dot on a new line
starts a variant expression in Oak.

The builder uses no boxes, heap allocation, closures or virtual dispatch. Its
value state and direct calls can be inlined and removed by the C optimizer;
that is an optimization opportunity, not a guarantee for every program or build
mode. A Linux amd64 CI regression compares a constant single-byte fluent chain's
`-O3` assembly with a direct constant return. Dynamic lengths still need bounds
checks, copying still performs work, and an unoptimized build may retain calls.
Native Apple Silicon optimizer validation remains separate work.

## Bounded array lists

The array-list API borrows initialized `[N]T` storage and a zero-initialized
`[1]ArrayListCursor`. `cursor[0].length` tracks the live prefix. Keep the cursor
paired with the same storage and pass its actual capacity to metadata operations.
This bootstrap API uses a separate cursor and span, like the ring; there is no
owning `ArrayList[T]` aggregate or allocator-backed growth yet.

| Operation | Result | Cost |
| --- | --- | --- |
| `array_list_push(cursor, storage, value)` | Inserted index, or `Full` | O(1) |
| `array_list_insert(cursor, storage, index, value)` | Inserted index, or `OutOfBounds` / `Full` | O(length - index) |
| `array_list_get(cursor, view, index)` | Value copy, or `OutOfBounds` | O(1) |
| `array_list_set(cursor, storage, index, value)` | Previous value, or `OutOfBounds` | O(1) |
| `array_list_pop(cursor, storage)` | Last value, or `Empty` | O(1) |
| `array_list_remove(cursor, storage, index)` | Removed value, preserving order | O(length - index) |
| `array_list_swap_remove(cursor, storage, index)` | Removed value, replacing it with the last element | O(1) |
| `array_list_clear(cursor, capacity)` | Logical reset; no erasure | O(1) |

Fallible operations return `Result[Payload,CollectionError]`. Removal outside the
live prefix returns `OutOfBounds`. Insert permits `index == length` and validates
the index before capacity. Errors preserve both length and every backing element.
Array-list get takes `[]T`; other element operations take `[*]T`. Generic calls
infer T from the arguments. Costs above exclude the size of an element copy.
Elements must be initialized, copyable values; no resource destruction or ownership
transfer is performed. Removal and clear leave stale bytes outside the live prefix.

## Intrusive lists and queues

Embed `slist: SListHook` and/or `dlist: DListHook` in a concrete node record.
Algorithms specialize for that record type and update its embedded hooks in place;
they never allocate node wrappers or copy payloads. The field names are the
bootstrap hook-selection convention. A node can participate in one singly linked
list and one doubly linked list simultaneously; multiple independently named hooks
of the same family and generic hook adapters are future work.

```oak
Task: type = struct {
  value: u32
  slist: SListHook
  dlist: DListHook
}
```

Back nodes with an initialized fixed array, and borrow it as `[*]Task`. Each list
uses a zero-initialized `[1]IntrusiveCursor`; call `intrusive_init(cursor, id)`
with a nonzero ID before use. IDs must be unique among live cursors operating on
the same pool and hook family. An ID is a caller-maintained membership label,
not a capability, generation counter, or cryptographic authority. Keep each cursor
paired with its pool and hook family; do not copy active cursors, mutate live hooks,
move/reorder linked nodes within the pool, or reuse an ID while its hooks remain linked.
Initialization rejects a nonempty cursor. Clear or pop/remove all nodes before reuse.

Links store `pool_index + 1`, with zero representing no link. Operation arguments
and successful results use ordinary zero-based pool indices. Each hook records its
owning list ID. Duplicate insertion returns `AlreadyLinked`, even into a different
list; removal through the wrong list or of a detached node returns `NotMember`.
Indices outside the pool return `OutOfBounds`; popping an empty list returns `Empty`.
These expected errors leave cursor, hooks and payloads unchanged.

| Operations | Cost |
| --- | --- |
| `slist_push_front`, `slist_push_back`, `slist_pop_front` | O(1) |
| `slist_remove` | O(length), finding the predecessor |
| `dlist_push_front`, `dlist_push_back`, `dlist_pop_front`, `dlist_pop_back`, `dlist_remove` | O(1) |
| `intrusive_queue_push`, `intrusive_queue_pop` | O(1), FIFO facade over singly linked hooks |
| `slist_validate`, `dlist_validate` | O(length), bounded full-chain validation |
| `slist_clear`, `dlist_clear` | O(length), validate then detach every member; return old count |

Push/remove take `(cursor, nodes, index)`; pop, validate and clear take
`(cursor, nodes)`. Push/pop/remove return `Result[u32,CollectionError]`. Successful
removal zeroes that hook's links and owner, preserving payload and the other hook.
All collections are sequential and require exclusive access. Metadata and touched
links are checked on ordinary operations; full validators additionally check the
whole forward chain, owner IDs, exact count/tail termination, and doubly linked
backlinks. Invalid internal state traps. This is not protection against forged
cursors, stale indices, ID collisions, or adversarial hook mutations.

Traverse from `cursor[0].head`; a nonzero link names `nodes[link - 1]`, whose hook's
`next` continues traversal. Doubly linked traversal may start at `tail` and follow
`prev`. Keep the pool and membership stable while traversing. No raw pointer bits,
PAC codes, heap objects or runtime dispatch tables are used.

See `examples/stdlib_intrusive_queue.oak` for a complete queue example.

## Intrusive transfer and splice

These operations move membership between two initialized cursors sharing the
same pool and hook family. Arguments are destination first, then source, then
`nodes`; single-node transfers also take a zero-based node index. Both cursor IDs
must be distinct and must obey the existing per-pool uniqueness contract.

| Operation | Result on success | Work |
| --- | --- | --- |
| `slist_transfer_front` / `slist_transfer_back` | Moved node index | O(source length), locating its predecessor |
| `dlist_transfer_front` / `dlist_transfer_back` | Moved node index | O(1) |
| `slist_splice_front` / `slist_splice_back` | Number of moved nodes | O(source length) |
| `dlist_splice_front` / `dlist_splice_back` | Number of moved nodes | O(source length) |
| `intrusive_queue_append` | Number of moved nodes | O(source length), FIFO append using singly linked hooks |

All return `Result[u32,ListTransferError]`. `SameList` rejects equal IDs, including
self-transfer and self-splice; this check precedes index validation. For single-node
transfer, `OutOfBounds` rejects indices outside the pool, and `NotMember` rejects
detached nodes or nodes belonging to another list. Expected errors preserve both
cursors and every node. They do not perform a remove followed by a recoverable
failed insertion: destination capacity and membership eligibility are checked first.

Splice preserves the source's order. Back splice yields `old destination ++ old
source`; front splice yields `old source ++ old destination`. The source becomes
empty and retains its ID for reuse. Splicing an empty source into a distinct
list succeeds with count zero and changes nothing. Each moved hook gets the
destination's owner ID, so subsequent removal through the old source returns
`NotMember`. Payloads and hooks of the other family remain unchanged.

The per-node owner update makes whole-list splice linear even though connecting
list endpoints takes constant work. Splice validates the complete bounded source
chain before retagging it; destination endpoint checks and the combined-count
check also run before mutation. Single transfers use the existing local checks
and removal rules. Both inputs must satisfy their full list invariants; these
operations are not a repair mechanism for forged cursors or arbitrary hook writes.

These are sequential operations, with no heap allocation or payload copies.
They are not atomic publication primitives: callers must provide any required
synchronization. For an executable scheduler-style batch transfer, see
`examples/stdlib_queue_transfer.oak`.

## Bounded min-priority heap

The `min_heap_*` functions implement a binary min-heap in caller-owned storage.
Entries are initialized, copyable records with a `priority: u64` field; other
fields carry the payload. The smallest priority is returned first. Calls
specialize for the concrete entry type, with direct comparisons and inline values.
No allocator, boxing, callback dispatch or automatic growth is involved.

```oak
Job: type = struct {
  priority: u64
  value: u32
}
```

Use an initialized `[N]Job` array and a zero-initialized `[1]MinHeapCursor`.
Keep that cursor paired with its storage. `cursor[0].length` is the live heap
prefix. Unlike intrusive lists, this heap reorders whole entries, so array
positions are not stable handles. Do not put linked intrusive nodes or unique
resources into it; a small entry containing a priority and an external pool
index can refer to a separately stored payload.

| Function | Success / error | Work |
| --- | --- | --- |
| `min_heap_push(cursor, storage, entry)` | New length, or `Full` | O(log n) |
| `min_heap_peek(cursor, view)` | Copy of minimum entry, or `Empty` | O(1) |
| `min_heap_pop(cursor, storage)` | Removes and returns minimum entry, or `Empty` | O(log n) |
| `min_heap_replace_top(cursor, storage, entry)` | Replaces and returns old minimum, or `Empty` | O(log n) |
| `min_heap_build(cursor, storage, count)` | Heapifies initialized prefix, returns count; `OutOfBounds` if count exceeds capacity | O(count) |
| `min_heap_clear(cursor, capacity)` | Logical reset without erasing storage | O(1) |
| `min_heap_validate(cursor, view)` | Checks cursor and every parent/child ordering relation | O(n) |

Push/build return `Result[u32,CollectionError]`; peek/pop/replace return
`Result[Entry,CollectionError]`. Mutating entry operations use `[*]Entry`; peek
and validate use `[]Entry`. Use lexical scopes to release a mutable borrow before
creating a read view. Metadata-only clear takes the actual backing capacity.

Full/empty/out-of-range failures preserve cursor length and every backing entry.
Replacing the top of an empty heap returns `Empty`; it does not insert. Build
permits count zero, discards the old logical heap, and rearranges only the given
initialized prefix; backing entries after that prefix remain unchanged. Removal
and clear leave stale entries outside the live prefix. Equal priorities have no
stable order; use unique priorities or encode a tie-breaker in the key when order
among ties matters. Priorities cover the full unsigned 64-bit range.

Entry copies contribute their ordinary value-copy cost to the bounds above.
The child-index calculation checks that a node has children before multiplying,
so u32 index arithmetic cannot wrap for a valid heap length. Cursor bounds are
checked on each operation. The heap-order invariant must hold before push/pop/
replace/peek; use build after externally changing priorities. Full validation is
explicit, and corrupted cursors or invalid ordering found by validation trap.
The sift helpers are implementation operations with bounds preconditions; direct
callers must establish the appropriate partial-heap invariant themselves.

This is a sequential queue: synchronization, stable handles, decrease-key,
arbitrary removal and intrusive heap membership are not implemented by this API.
See `examples/stdlib_priority_queue.oak` for an executable example.

## Bounded circular deque

Inspired by SerenityOS AK's [CircularDeque](https://github.com/SerenityOS/serenity/blob/master/AK/CircularDeque.h),
Oak's deque supports both FIFO and LIFO use, with constant-time access at either
end and by logical index. The implementation is written in Oak and uses the
existing caller-owned storage convention. Unlike AK's overwriting enqueue,
Oak returns `Full` and preserves the queue when capacity is exhausted.

Pair a zero-initialized `[1]DequeCursor` (`head`, `count`) with initialized storage
of copyable `T`. Keep the same backing storage and capacity for its active lifetime.
Logical index zero is the front; values may wrap around the physical array.
Zero capacity is valid: pushes return `Full`, pops/front/back return `Empty`,
and indexed operations return `OutOfBounds`.

| Operation | Success | Error |
| --- | --- | --- |
| `deque_push_front/back(cursor, storage, value)` | New count | `Full` |
| `deque_pop_front/back(cursor, storage)` | Removed value | `Empty` |
| `deque_front/back(cursor, view)` | Copy of endpoint | `Empty` |
| `deque_get(cursor, view, index)` | Copy at logical index | `OutOfBounds` |
| `deque_set(cursor, storage, index, value)` | Previous value | `OutOfBounds` |
| `deque_clear(cursor, capacity)` | Resets head and count | Invalid cursor traps |

Fallible operations return `Result[_, CollectionError]`. Every error preserves
both cursor fields and all backing entries. Pop and clear leave stale bytes in
storage; they do not erase memory or run resource destruction. All operations
are O(1), excluding ordinary element-copy cost. They neither allocate nor shift
other entries. Generic specialization uses concrete values without boxing.

`deque_check` validates bounds on every operation; an empty cursor can have a
nonzero head when capacity is nonzero. `deque_offset` is a checked arithmetic
helper requiring head and offset below capacity. Its subtraction-based wrap
avoids overflow even at the maximum u32 capacity. Direct callers must preserve
cursor/storage pairing and the logical contents; the cursor is not a borrow or
an ownership token. No concurrent access, stable element handles, or intrusive
membership is provided. Existing `ring_*` APIs retain their original contracts.

## Dense reusable ID pool

SerenityOS AK's [IDAllocator](https://github.com/SerenityOS/serenity/blob/master/AK/IDAllocator.h)
provides the inspiration for explicit ID allocation and release. Oak's bounded
variant uses a caller-owned bitmap instead of AK's random selection and hash
table. IDs are deterministic zero-based slots in `[0, limit)`: allocation always
selects the lowest free ID. This suits fixed kernel object tables and database
request pools; use an explicit reservation to exclude a slot such as zero.

Supply at least `bitset_storage_bytes(limit)` initialized bytes, zeroed or cleared
before first use. A set bit means allocated. There is no separate cursor or hidden
allocator state. Keep the bitmap and limit paired while IDs are live; changing the
limit can expose previously unused bits. Do not mutate the bitmap independently
of its users.

| Operation | Success | Work |
| --- | --- | --- |
| `id_pool_allocate(storage, limit)` | Lowest free ID | O(limit), skips full bytes |
| `id_pool_reserve(storage, limit, id)` | Specified newly allocated ID | O(1) |
| `id_pool_release(storage, limit, id)` | Released ID | O(1) |
| `id_pool_contains(view, limit, id)` | Whether ID is allocated | O(1) |
| `id_pool_clear(storage, limit)` | Logical limit | O(ceil(limit / 8)) |

Results use `IdPoolError`: `StorageTooSmall`, `Full`, `OutOfBounds`,
`AlreadyAllocated`, or `NotAllocated`. Storage size is checked first. Reserve
rejects an occupied ID; release rejects a free ID. Every error leaves all bytes
unchanged. Operations ignore and preserve unused high bits in the final byte and
all spare bytes, including clear. Limit zero is valid and always full; the full
u32 argument range is checked without overflowing the byte-size calculation.

IDs are reusable numeric slots, not generation-checked handles, capabilities,
random identifiers, or PAC-authenticated pointers. Release followed by allocation
can return the same number. Applications needing stale-handle detection must
track generations separately. Clear invalidates all logical allocations and must
only be used when their users have been retired. Synchronization is caller-owned.

See `examples/stdlib_deque_ids.oak` for a compiled, executed example combining a
record-valued deque with an ID pool. Both structures operate without allocation.
Further AK-inspired work includes hash tables/maps, intrusive ordered trees, and
segmented/disjoint storage; these are not implemented by this addition.

## Sorting and searching

`sort_span[T](items)` sorts a span in place through the element type's `<`
with a pattern-defeating quicksort (Peters 2021, the algorithm behind Go's
`slices.Sort` and Rust's `sort_unstable`): insertion sort at twelve elements
or fewer, median-of-three pivots and Tukey's ninther from fifty elements, a
partition that notices already-partitioned ranges, a partial insertion sort
that finishes nearly sorted ranges in five swaps, an equal-elements
partition that makes many duplicates linear, pattern-breaking swaps after an
unbalanced split, and heapsort once the depth budget (the bit length of the
length) is spent, so the worst case is O(n log n) and sorted, reversed, and
all-equal inputs are O(n). The recursion is an explicit 48-frame stack (the
smaller side is sorted first, so one frame per halving is outstanding).
`sort_span_budget[T](items, depth)` exposes the budget; `sort_insertion`
(stable) and `sort_heap` are also exported. `sort_is_sorted[T](view)` checks
non-decreasing order, `sort_search[T](view, key)` is a binary search returning
`Option[u32]`, `sort_lower_bound[T](view, key)` the first index not less than
the key (the insertion point), `sort_dedup[T](span)` compacts a sorted span
to one element per run and returns the new length, and `sort_reverse[T]`
reverses in place. No allocation; `sort_span` is not stable, insertion sort
is. On an Apple M4 Max (`benchmarks/stdlib`, 100k u32), `sort_span` runs at
0.92× Go's `slices.Sort` on random input, 1.1× on reversed, and 1.4× on
sorted (heapsort was 1.2×, 21×, and 22×).

## Variable-length integers

`varint_encode(dst, offset, value)` writes unsigned LEB128 (one to ten bytes,
`varint_size(value)`), `varint_decode(src, offset)` reads it back as a
`VarintValue { value, next }` and rejects truncated forms, over-long forms,
and zero-padded spellings (`80 00` is not `0`), so every value has exactly
one accepted encoding, the one `varint_encode` writes — proved on the Lean
extraction (`Oak/Stdlib/VarintLaws.lean`, `round_trip` and `canonical`);
`zigzag_encode`/`zigzag_decode` map
signed to unsigned so small magnitudes stay short, and
`varint_encode_signed`/`varint_decode_signed` compose the two. Errors are the
closed `VarintError`; a failed write leaves the destination unchanged.
`varint_ok`/`varint_value` and `varint_signed_ok`/`varint_signed_value` unwrap
decode results (zero on error) and `varint_written` unwraps an encode result,
for callers that have already checked the input.

## Deterministic random numbers

`random_seed(seed)` derives a xoshiro256** state (`Xoshiro`) through
SplitMix64; `random_next(state)` yields 64 bits, `random_below(state, bound)`
a uniform value below the bound by rejection (no modulo bias),
`random_range(state, low, high)` an inclusive range, `random_bool`,
`random_fill(state, dst)` random bytes, and `random_shuffle[T](state, span)` a
Fisher-Yates permutation. Bit-exact across the interpreter and every backend;
not a cryptographic source. Tests draw from the choice tape instead
(`import(testing)`).
## URI references

`url_parse(src)` splits a URI or relative reference (RFC 3986 §3, Appendix B)
into a `Url` of byte ranges — scheme, userinfo, host, port, path, query,
fragment, each a `UrlRange { start, end, present }` into the source — and
validates every component against its grammar: scheme characters (§3.1),
userinfo, reg-name or bracketed IP-literal host, digits-only port (§3.2),
path, query and fragment character classes with `%XX` escapes needing two hex
digits (§3.3–§3.5), and no `:` in a relative reference's first segment
(§4.2). Errors are the closed `UrlError` (`InvalidScheme`, `InvalidHost`,
`InvalidPort`, `InvalidCharacter`, `InvalidPercentEncoding`,
`DestinationTooSmall`). Nothing is allocated or copied: callers slice the
source themselves (`src[range.start:range.end]`), since a function may not
return a view (OAK-B0109), as in the strings package. `url_port_number` reads
the port as `Option[u32]` (None above 65535), `url_is_absolute` (§4.3) and
`url_is_relative` classify. `url_remove_dot_segments(dst, path)` applies
§5.2.4 into caller storage (the output never exceeds the input, so `dst` must
hold `len(path)` bytes, checked before the first store), and
`url_resolve(dst, base, reference)` writes the target of a reference against
an absolute base (§5.2.2 strict, §5.2.3 merge, §5.3 recomposition; `dst` must
hold `len(base) + len(reference) + 1` bytes). `url_query_next(query, begin)`
iterates `&`-separated `key=value` pairs as ranges; keys and values stay
percent-encoded — decode them with the `encoding` package's
`percent_decode`. Properties in `examples/testing/url_test.oak`: a generated
reference parses back to the ranges it was built from, and dot-segment
removal is idempotent and leaves no `.` or `..` segment.

## UUIDs

`stdlib/uuid.oak` (`import("uuid")`, also in the flat prelude) makes and
reads RFC 9562 values in caller storage: a UUID is sixteen bytes of a span or
view. `uuid_v4(state, dst)` draws 122 random bits from a `random` generator
and stamps version 4 and the RFC variant; `uuid_v7(unix_millis, state, dst)`
writes the 48-bit millisecond timestamp big-endian, version 7, 74 random
bits, and the variant, so version 7 values sort by time under
`uuid_compare` (bytewise). `uuid_nil`/`uuid_max` write the two constants,
`uuid_version`/`uuid_variant`/`uuid_v7_millis` read the fields as `Option`
(None unless the view is sixteen bytes and, for the timestamp, version 7).
`uuid_format(dst, src, upper)` writes the 8-4-4-4-12 form (`UUID_TEXT_SIZE`
bytes, lowercase unless asked) and `uuid_parse(dst, src)` accepts exactly
that form in either case, validating the whole input before the first store;
braces, the URN prefix, and the 32-digit form are rejected. Errors are the
closed `UuidError = InvalidLength | InvalidCharacter | DestinationTooSmall |
TimestampOutOfRange` with `uuid_ok`, `uuid_written`, `uuid_failure`
unwrappers. The `random` generator is xoshiro256** and not cryptographic, so
a version 4 value from this package identifies things but must not serve as
a secret or a capability token; version 3 and 5 (MD5/SHA-1) are absent
because the `hash` package carries neither digest.
## Paths and glob patterns

`stdlib/path.oak` (`import("path")`, also in the flat prelude) is Go's `path`
package over caller-owned bytes: slash-separated, no OS-specific behavior.
`path_clean(dst, src)` applies Go's four rules (collapse slashes, drop `.`,
resolve inner `..`, drop a rooted leading `..`; the empty path is `.`),
`path_join(dst, a, b)` joins two elements and cleans (empty elements are
skipped; both empty is empty), and `path_dir(dst, src)` writes the cleaned
directory. All three clean in place inside the destination, because Go's
algorithm never writes past its read position, so a destination as long as
the input (one byte for the empty path) always fits and is checked before
the first store. `path_base`, `path_ext`, `path_split` and the iterator
`path_next_component(src, begin)` return `PathRange`s into the source that
callers slice themselves (a function may not return a view); the base of an
empty path is the empty range where Go spells `.`. `path_is_abs` tests the
leading slash.

`path_match(pattern, name)` is Go's `path.Match`: `*` any run of non-slash
characters, `?` one non-slash character (a whole UTF-8 scalar, as Go matches
runes), `[class]` and `[^class]` with `lo-hi` ranges and `\` escapes, `\c`
for a literal; the whole name must match and a malformed pattern is
`Err(BadPattern)` even after the name has already failed (Go 1.16+
semantics). `path_match_glob` adds `**` as a whole component matching zero
or more components, so `a/**/b` matches `a/b` and `a/x/y/b`, `**/b` matches
`b`, and `a/**` matches `a` and everything below it; components are compared
pairwise with `path_match`, so `a//b` and an absolute name keep their slash
structure. Matching backtracks over star positions without recursion or
allocation. Errors are the closed `PathError = BadPattern |
DestinationTooSmall` with `path_ok`, `path_written`, `path_failure`,
`path_matched`, `path_match_failure` unwrappers, and `path_match_code` /
`path_match_glob_code` return 0, 1 or 2 for callers that prefer a code.
## Floating-point text

`stdlib/float.oak` (`import("float")`, also in the flat prelude) converts
f64 and f32 to and from decimal text exactly, with the algorithm Go's
`strconv` uses on its slow path: an 800-digit decimal in caller storage,
shifted by powers of two, so no floating-point arithmetic takes part and
every backend agrees byte for byte with `strconv.FormatFloat` and
`strconv.ParseFloat`.

- `float_format(dst, value)` writes the shortest digit string that parses
  back to the same f64, in Go's `'g'`/-1 spelling: the exponent form when
  the decimal exponent is below -4 or at least 6 (`1e+06`, `100000`,
  `1e-05`, `0.0001`), exponents with at least two digits, `NaN`, `+Inf`,
  `-Inf`, and `-0` for the negative zero. `FLOAT_TEXT_SIZE` (32) bytes hold
  any shortest spelling. `float_format_fixed(dst, value, digits)` is Go's
  `'f'` with that many fraction digits and `float_format_exp` its `'e'`,
  both rounded half to even on the exact binary value (so `2.5` with no
  digits is `2`, `0.125` with two is `0.12`). `float_format_f32` and the
  `_fixed_f32`/`_exp_f32` forms do the same for f32 (shortest for the f32
  format, not the f64 one).
- `float_parse(src)` is the f64 nearest to the exact decimal value of the
  text, ties to even, subnormals and the range ends included. The whole view
  must be one number: optional sign, digits with an optional fraction,
  optional `e`/`E` exponent, or `inf`/`infinity` (optionally signed) and
  `nan` in any case; anything else — an empty view, a lone `.`, digit
  separators, hexadecimal floats, trailing bytes — is `InvalidSyntax`. A
  magnitude beyond the largest finite value is `OutOfRange`
  (`float_parse_saturating` returns the signed infinity instead); underflow
  rounds to zero or a subnormal without error. `float_parse_f32` rounds once
  from the decimal to f32 (never through an f64), with the same saturating
  variant.
- Errors are the closed `FloatError = InvalidSyntax | OutOfRange |
  DestinationTooSmall`; every format checks the destination before its
  first store. Unwrappers: `float_ok`/`float_written`/`float_failure` for
  format results and `float_parse_ok`/`float_parse_value`/
  `float_parse_failure` (plus `_f32` forms) for parse results.

`compiler/e2e_stdlib_float_test.go` checks the classic hard cases (`0.1`,
`5e-324`, the `2.2250738585072011e-308` hang value, `9007199254740993`
rounding to even, `1e23`, the exponent-form threshold, specials, the
subnormal boundary midpoints, thousand-digit inputs) in every form against
Go, compiled and interpreted, and a differential test formats and parses
thousands of random bit patterns, random decimal spellings, and exact
midpoints between adjacent doubles, comparing every line with `strconv`.
`examples/testing/float_test.oak` states the round trips as properties.
Deviations from Go: digit-separating underscores and hexadecimal floats are
rejected rather than accepted.

## Unicode normalization

`stdlib/normalize.oak` (`import("normalize")`, also in the flat prelude)
implements the four normalization forms of UAX #15 at Unicode 17.0.0 over
UTF-8 views into caller-owned spans: `normalize_nfd` and `normalize_nfkd`
decompose (canonical, or canonical plus compatibility, always the full
recursive decomposition, Hangul syllables algorithmically) and put combining
marks in canonical order; `normalize_nfc` and `normalize_nfkc` then recompose
primary composites under the blocking rule of D117, composition exclusions
and Hangul included. `normalize_form(dst, src, form)` selects a form by the
`NORMALIZE_NFD .. NORMALIZE_NFKC` constants. Every function returns
`Result[u32, NormalizeError]` with the count written; the closed error type is
`InvalidEncoding | DestinationTooSmall | RunTooLong`. Nothing allocates and
every store follows its length check, but the pass streams: when the
destination is too small the bytes written before the failure stay, so
callers size the destination with the exact `normalize_nfd_size` /
`normalize_nfc_size` / `normalize_nfkd_size` / `normalize_nfkc_size` (a
counting pass over the same algorithm) or allow 18 × 4 bytes per input scalar,
the longest decomposition at the widest encoding. The algorithm holds one run
— a starter and the marks after it — in a `NORMALIZE_RUN_LIMIT` (256) scalar
buffer; text with more consecutive non-starters than that (UAX #15's
stream-safe format caps them at 30) is refused as `RunTooLong` rather than
normalized wrongly. `normalize_is_nfd`/`normalize_is_nfkd` are the quick check
of §9 (decisive for the decomposed forms); `normalize_is_nfc`/
`normalize_is_nfkc` run the quick check and, only when a MAYBE scalar leaves
it undecided, the full pass compared byte for byte against the input. A block
table marks the 150 of 4352 blocks that hold any property, decomposition, or
Hangul syllable, so scalars elsewhere skip every lookup, and a run of ASCII
copies straight through. `normalize_ccc`, `normalize_flags`,
`normalize_compose_pair`, and `normalize_is_plain` expose the tables. The
tables come from `extract_normalize.py` (UnicodeData.txt,
DerivedNormalizationProps.txt) through `unicode17_normalize.json` and
`generate_normalize.py`; `testdata/NormalizationTest-17.0.0.txt` is checked in
and every one of its 20,034 lines passes all five-column invariants in
`compiler/e2e_stdlib_normalize_test.go`, `e2e_stdlib_normalize_laws_test.go`
compares the compiled code with an independent Go transliteration on random
sequences, and `spec/lean/Oak/Normalization.lean` proves canonical ordering
is a stable sorted permutation, NFD idempotent, and the NFC laws (`nfd (nfc x)
= nfd x`, NFC idempotent) for any data that is closed under decomposition
and whose primary composites invert it; `spec/lean/Oak/Stdlib/Normalize17.lean`
discharges both for the Unicode 17.0.0 tables (generated as key trees by
`generate_normalize.py`, decided in the kernel, with the Hangul syllables by
arithmetic), so the laws hold unconditionally for the shipped data. Invalid
UTF-8 is `InvalidEncoding`, never normalized.

## Grapheme clusters

`stdlib/grapheme.oak` (`import("grapheme")`, also in the flat prelude)
segments UTF-8 text into extended grapheme clusters, the user-perceived
characters of UAX #29 section 3.1.1 at Unicode 17.0.0: a base with its
combining marks, a Hangul syllable spelled as jamo, an emoji ZWJ sequence, a
flag pair, an Indic conjunct. `grapheme_next(src, at)` returns the byte
offset where the cluster starting at `at` ends (`len(src)` at the end), so
walking from 0 partitions the text; `grapheme_count(src)` is the length of
that walk and `grapheme_is_boundary(src, at)` whether the walk lands on
`at`. `at` must be a boundary reached from 0, because GB9c, GB11 and the
Regional_Indicator parity of GB12/GB13 count from the start of the scan.
An undecodable byte is its own cluster, so segmentation is total over any
byte view. `grapheme_class(scalar)` is the combined property word `gcb |
incb << 8 | pictographic << 10` read by `grapheme_gcb`, `grapheme_incb` and
`grapheme_is_pictographic`, with the `GB_*` and `INCB_*` constants naming the
values; the table (`grapheme_table`, 1631 ranges) is generated from the
checked-in extract `unicode17_grapheme.json` by `generate_grapheme.py`, and
the extract from the UCD files by `extract_grapheme.py`.

The rules run as a state machine — `GraphemeState { prev, ri_run, pict,
conjunct }` with `grapheme_initial`, `grapheme_breaks(state, props)` and
`grapheme_advance(state, props)` exported — so each decision is one table
lookup and a bounded state, no allocation, no recursion, no lookback.
`spec/lean/Oak/GraphemeBreak.lean` states the rules GB3 to GB13 and GB999
as scans over the preceding text (`ruleBreak`, the annex's wording) and the
machine as `breaks`/`advance` folded over the text (`machineBreak`), and
proves `machine_agrees`: for every history of well-formed symbols (an
Extended_Pictographic or InCB=Consonant scalar has class Other, a Linker has
class Extend, InCB=Extend has class Extend or ZWJ — the shape the UCD
guarantees and the Go law test checks against the table) the two decide
every position identically. `compiler/e2e_stdlib_grapheme_test.go` runs the
hand-picked cases, the qualified import, and every line of the official
`GraphemeBreakTest-17.0.0.txt` (`stdlib/testdata`); the law test
`compiler/e2e_stdlib_grapheme_laws_test.go` enumerates every sequence of
five symbol shapes (18^5) through the compiled machine and compares each
boundary decision with an independent Go transliteration of `ruleBreak`.
`examples/testing/grapheme_test.oak` states the partition, count and ASCII
properties over tape-generated text. Reverse iteration (`grapheme_prev`) is
absent: the parity and conjunct rules need unbounded lookback from the
right, so callers walk forward from 0.

## Strings and Unicode text

The [strings API](STRINGS.md) is executable through `import(std)`: strict
UTF-8/16/32 codecs, ASCII validation, Unicode 17 full casing and case folding,
searching, trimming, split/fields iteration, range-based joining, replacement,
repetition, byte order marks, UTF-16 as bytes in either byte order, Latin-1,
signed and radix number parsing and formatting, and a bounded fluent text
builder. All outputs use
caller-provided storage. `text_literal("hello")` supplies readable static UTF-8
byte views through ordinary borrowing. The placeholder string examples have been
replaced with compiled programs; see `examples/stdlib_strings.oak`.

## Verification and remaining work

The per-package status — Go end-to-end tests, Oak property and simulation
tests, the oracle each package is compared against, whether its Lean
extraction is committed, which laws are proved universally, which are only
decided on inputs, what the faithfulness harness covers, and the latest
benchmark ratio — is one table in [VERIFICATION.md](VERIFICATION.md). That
file is derived from the tree and names the theorem and test functions, so
it is the place to look before believing a sentence in this README.

Three kinds of evidence back the packages, and they are not interchangeable.
For `sort`, `varint`, `random`, `uuid`, and the hexadecimal and base64
codecs the laws are theorems about the Lean image `oak build -lean` produces from the same
source the C backend compiles (`docs/spec/95-extraction.md`): a drift test
keeps the committed image current and `TestLeanStdlibFaithful` runs the image
and the compiled program on one corpus and compares them byte for byte, so
the remaining assumptions are the extractor's stated modeling choices and the
compiler. For `grapheme`, `normalize`, `causal_frontier`, the interval time
readings, and the IO port the theorems are about a hand-written model of the
published rules, and a Go law test or a transliteration relates the Oak code
to that model on enumerated or random inputs. Everything else — the prelude
collections, `strings`, `json`, `hash`, `math`, `mx`, `url`, `path`,
`float`, `time`'s calendar, the simulation packages — is checked by
implementation tests against sequence models, Go's standard library,
conformance files, or reference implementations; those are not refinement
proofs.

The standard-library workflow (`.github/workflows/stdlib.yml`) runs the
package tests, the generated-table checks, the extraction drift test, and
every non-compiler package under the race detector; the compiler package's
race run is sharded in `ci.yml`; the Formal Verification workflow builds
`spec/lean` and runs the faithfulness harness. Native Apple Silicon
execution, PAC/tag representations, capability transfer/revocation,
allocator-backed pools, intrusive trees/hash tables, concurrent rings,
broader collections, and persistence protocols remain separate work;
importing this module does not implement them.

See [Oak collection ports](COLLECTION_PORTS.md) for Bloom/counting Bloom filters,
u64-key hash maps and sets, bitset algebra, validated flags, and the remaining OS
library parity work.

## `math`: transcendental functions (`import("math")`)

`stdlib/math.oak` implements `exp`, `exp2`, `expm1`, `log`, `log2`, `log1p`,
`sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`,
`tanh`, `asinh`, `acosh`, `atanh`, and `pow` over `f64`, plus `exp_f32` …
`pow_f32` over `f32`, entirely in Oak (docs/spec/20-types.md section
11.3.6). The algorithms are fdlibm's (as carried by musl), with the
Cody-Waite split constants spelled as hexadecimal literals generated from
the fdlibm bit patterns; the trigonometric functions reduce huge arguments
(at or beyond 2^20 pi/2) by a Payne-Hanek multiplication against the
relevant limbs of 2/pi in exact integer arithmetic. Because every primitive
they use is correctly rounded, the interpreter and every backend compute
identical bits — the bit-exact transcendental implementation a reproducible
training run needs.

Contract: error within 1 ulp of the correctly rounded result for
`exp exp2 expm1 log log2 log1p sin cos tan asin acos atan pow`, within 2 ulp
for `atan2 tanh sinh cosh asinh acosh atanh` (compositions of the 1-ulp
functions); the `_f32` forms compute at `f64` and round once. `pow` and
`atan2` follow IEEE 754-2019 / C99 Annex F for their special values, and
`pow` is exact for representable integer powers. `compiler/e2e_math_test.go`
is the fourth witness: an arbitrary-precision reference over special
points, interval boundaries, random arguments, the nearest doubles to
multiples of pi/2, and the Annex F cases, failing on any case beyond the
bound and on any difference between compiled and interpreted results.

## `hash`: SHA-256, BLAKE3, and CRC-32C (`import("hash")`)

`stdlib/hash.oak` implements SHA-256 (FIPS 180-4), BLAKE3 (hash mode,
32-byte output), and CRC-32C (the
Castagnoli polynomial `0x82F63B78`, reflected, all-ones initial value,
final complement — RFC 3720 appendix B.4) in Oak over the total fixed-width
arithmetic — CRC-32C table-driven, SHA-256 compressing whole blocks in
place from the input, BLAKE3's quarter round by value, every block and
table access proven by the extent facts (`benchmarks/kernels/RESULTS.md`
measures them against Rust and Go) — so the interpreter and every backend
compute the same bits and
`oak test` can check a frame's checksum or a hash chain without a foreign
implementation. Everything lives in caller-owned or bounded local storage:
no allocation, every store bounds-checked.

SHA-256 is incremental: `sha256_init(): Sha256State`, `sha256_update(state,
view): Sha256State` over any number of pieces, `sha256_final(state, out:
[*]u8): Bool` writes the 32-byte big-endian digest and is false when `out`
is shorter; `sha256(view, out)` is the one-shot form. CRC-32C is a running
value: `crc32c(view): u32`, and `crc32c_update(crc, view)` continues a
finished checksum across pieces, so `crc32c_update(crc32c(a), b)` is the
checksum of `a ++ b`. BLAKE3 has the same incremental shape —
`blake3_init`, `blake3_update`, `blake3_final(state, out)` — and a one-shot
`blake3(view, out)`; the state carries the open chunk and the chaining-value
stack (room for the 54 levels a 64-bit length can need), and the tree is the
specification's: 1024-byte chunks, parents merged by the chunk counter's
trailing zeros, the last parent taking the root flag.

On AArch64 the two hot kernels run through the CPU's instructions:
`stdlib/hash.arm64.oakasm` (embedded and attached by the loader whenever
`hash` is imported, its function names rewritten to the package's internal
names) realizes `crc32c_step7` — seven `crc32cx` steps over the 64-bit
words `crc32c_update` folds 56 bytes at a time — and `sha256_block_hw` — one
compression through `sha256h`/`sha256h2`/`sha256su0`/`sha256su1`, the state
read from and written to a span and the block and round constants read
through views under the assembler checker's dominating length guards. Each
unit pairs with an Oak declaration that keeps its portable body, so the body
is the definition: the seam checker admits the unit only within the
declared registers and proven memory, the extraction and the interpreter see
the Oak body, non-AArch64 targets and `-DOAK_PORTABLE_INTRINSICS` builds run
it, and the differential tests (`compiler/e2e_stdlib_crc_sha_hw_test.go`)
plus the faithfulness harness compare the two paths byte for byte. The CRC
and SHA-2 instructions have no semantics in the asm verifier, so their
verdicts are "trusted" (`94-assembler.md` §5), which is exactly what the
differential tests cover. An AArch64 build requires FEAT_CRC32 and
FEAT_SHA256 (every Apple M-series core and Armv8.1+ server core has both;
a core without them takes SIGILL at the first call — build with
`-DOAK_PORTABLE_INTRINSICS` for such a target). Measured on an M4 Max
(`benchmarks/stdlib/RESULTS.md`): CRC-32C at parity with Go's hardware path
(0.97×, from 20×), SHA-256 within 1.26× (from 7.3×); the remaining SHA gap
is one call and one 96-byte state copy per 64-byte block. BLAKE3 stays
portable.

`compiler/e2e_hash_test.go` checks the FIPS known-answer vectors, the
RFC 3720 CRC-32C check value (`0xE3069283` for `"123456789"`), and random
inputs at every length class around the 64-byte block and 56-byte padding
boundary against Go's `crypto/sha256` and `hash/crc32`, compiled and
interpreted, one-shot and split across an update boundary. BLAKE3 is checked
against a compact reference written from the specification in the test,
itself anchored to the official vectors for the empty and one-byte inputs,
at every tree shape that matters: partial and full blocks, one chunk, the
first parent, an odd chunk count, a full power-of-two tree, and larger
random inputs.

For the big-endian frame header, the core prelude already has
`bytes_read_u16_be/u32_be/u64_be(view, offset): Result[T, EndianError]` and
`bytes_write_*_be(span, offset, value)`, alongside the little-endian forms.

The package extracts whole to Lean (`spec/lean/Oak/Stdlib/HashExtracted.lean`,
regenerated by the drift test) and `TestLeanStdlibFaithful` compares the
extracted CRC-32C and SHA-256 with the compiled program on a corpus; no laws
about the digests are proved yet (`VERIFICATION.md`).

## `mx`: MXFP4 blocks (`import("mx")`)

`stdlib/mx.oak` implements the OCP Microscaling (MX) MXFP4 block format
in Oak (`docs/spec/20-types.md` §11.3.1a): thirty-two E2M1 elements — sign,
two exponent bits, one fraction bit, the eight magnitudes 0, 0.5, 1, 1.5,
2, 3, 4, 6 — packed two to a byte under one E8M0 scale (an unsigned
exponent with bias 127; `0xFF` is NaN). `Fp4Block` is a proven 17-byte
`struct { scale: u8, packed: [16]u8 }`; element `i` sits in `packed[i / 2]`,
even indices in the low nibble.

- `fp4_round_f32(x)` rounds to the nearest E2M1 code, ties to even;
  magnitudes past 6 clamp to 6 (the format has no infinity), NaN is zero,
  infinities clamp with their sign.
- `fp4_widen(code)` and `e8m0_widen(code)` are exact.
- `fp4_scale_of(values)` is the OCP MX v1.0 §6.3 block scale: the largest
  power of two at or below the largest magnitude, divided by 4, clamped to
  the E8M0 range; an all-zero block scales by 1.
- `fp4_quantize(values: [32]f32)` divides by the scale (an exact power of
  two) and rounds each element; `fp4_get(block, i)` and
  `fp4_dequantize(block)` multiply back, exact except where the product
  leaves the `f32` range.

Everything is `f32` and `u32` bit work, so the interpreter and the backends
agree bit for bit. `compiler/e2e_mx_test.go` checks every element code,
every rounding tie, the scale range, the layout, and a 64-block
pseudo-random sweep against a Go rendering of the same arithmetic,
compiled and interpreted. Block arithmetic is deliberately absent: a
kernel widens to `f32` and computes there.

## `encoding`: hex, base64, base32, percent (`import("encoding")`)

`stdlib/encoding.oak` implements the binary-to-text codecs a wire protocol
or a storage format reaches for — hexadecimal, base64 and base32 in the
RFC 4648 alphabets, and RFC 3986 percent-encoding — in Oak over borrowed
bytes, on the `strings` contract: input as a view `[]u8`, output into a
caller-owned span `[*]u8`, every function returning
`Result[u32, EncodingError]` with the count written, and every `_size`
function validating the input without writing. Nothing allocates; a
destination that is too short is reported before the first store, so a
failed call leaves the destination unchanged. The package is also part of
the flat `import(std)` prelude.

- `EncodingError: type = InvalidCharacter | InvalidLength | InvalidPadding
  | NonCanonical | DestinationTooSmall | SizeOverflow`, with
  `encoding_error_code` (1 to 6) and the `Result` helpers `encoding_ok`,
  `encoding_value` (0 on error) and `encoding_failure` (the code, 0 on
  success).
- Hex: `hex_encode(dst, src, upper)`, `hex_decode(dst, src)` (either case
  accepted), `hex_encoded_size(len)`, `hex_decoded_size(src)`; an odd
  length is `InvalidLength`, a non-digit `InvalidCharacter`. `hex_digit`
  and `hex_value` read the per-symbol tables.
- Base64 (RFC 4648 §4 and §5): `base64_encode(dst, src, url, pad)` selects
  the standard (`+/`) or URL-safe (`-_`) alphabet and optional `=`
  padding; `base64_decode(dst, src, url)` is strict — one alphabet, padding
  either complete or absent, a length of 1 mod 4 is `InvalidLength`,
  misplaced or excess `=` is `InvalidPadding`, and nonzero trailing bits in
  the final symbol are `NonCanonical`. `base64_encoded_size(len, pad)` and
  `base64_decoded_size(src, url)`.
- Base32 (RFC 4648 §6 and §7) with the same shape: `base32_encode(dst, src,
  hex, pad)`, `base32_decode(dst, src, hex)` (lowercase accepted),
  `base32_encoded_size(len, pad)`, `base32_decoded_size(src, hex)`; `hex`
  selects the base32hex alphabet.
- Percent (RFC 3986): `percent_encode(dst, src, keep)` leaves the
  unreserved set (`ALPHA DIGIT - . _ ~`) and every byte in `keep` as is and
  escapes the rest as uppercase `%XX`; `percent_decode(dst, src,
  plus_as_space)` accepts either hex case and decodes `+` as a space only
  when asked, and a `%` not followed by two hex digits is
  `InvalidCharacter`. `percent_encoded_size(src, keep)` and
  `percent_decoded_size(src, plus_as_space)`.

Every symbol lookup is a 256-entry table read (`stdlib/generate_codec_tables.py`
emits the tables into `encoding.oak`; CI re-runs it and diffs). A decoder
makes two passes by design: the first ORs every byte's table value, which is
below the alphabet size exactly when every byte is valid, so the whole
input is validated before the first store and a rejected input leaves the
destination untouched; the second decodes four base64 symbols per 24-bit
word (two hex digits per byte) without re-checking. The error a rejected
body reports keeps its order: misplaced `=`, then a length no encoder
produces, then a character outside the alphabet. On an M4 Max the compiled
C encodes and decodes base64 and hex within 25% of Go's `encoding/base64`
and `encoding/hex`.

Sizes are `u32`; an input whose encoding would not fit is `SizeOverflow`
rather than a wrapped count. `compiler/e2e_stdlib_encoding_test.go` checks
the RFC 4648 §10 test vectors for base64, base32 and base32hex, padded and
unpadded, the URL alphabet against the standard one, hex in both cases, the
percent cases including a kept set and `+`, every rejection class with the
destination shown unchanged, and the qualified `import("encoding")` form.
`examples/testing/encoding_test.oak` is the round-trip property over
tape-generated bytes for every codec and alphabet. Line wrapping, the
`base64` MIME dialect, and the non-strict "ignore whitespace" decoders are
deliberately absent.
## `time`: instants, civil time, RFC 3339 (`import("time")`)

`stdlib/time.oak` gives programs a notion of time without a clock: an
`Instant { nanos: i64 }` is nanoseconds since the Unix epoch, wherever the
value came from (the operating system, a message, a simulation's `SimClock`),
and a `Duration { nanos: i64 }` is a signed span. Both cover 1677-09-21 to
2262-04-11 around the epoch, and every arithmetic step is checked over the
prelude's `i64_checked_*` rows, so overflow is `Err(Overflowed)`, never a
wrap. The error type is closed: `TimeError = Overflowed | InvalidCivil |
InvalidFormat | InvalidOffset | InvalidDuration | DestinationTooSmall`.
Nothing allocates; text goes into caller-owned spans.

- **Durations**: `duration_nanos/micros/millis/seconds/minutes/hours` (the
  scaled constructors return `Result`), `duration_as_micros/millis/seconds/
  minutes/hours` (whole units toward zero), `duration_add`, `duration_sub`,
  `duration_scale`, `duration_negate` (the minimum has no negation),
  `duration_compare`.
- **Instants**: `instant_nanos`, `instant_seconds`, `instant_add`,
  `instant_sub`, `instant_since(a, b)` (`a - b`), `instant_compare`,
  `instant_unix_seconds` (floored) and `instant_subsecond_nanos`.
- **Calendar**: `Civil { year: i32, month: u8, day: u8, hour: u8, minute:
  u8, second: u8, nanos: u32 }` in the proleptic Gregorian calendar (year 0
  and negative years included, so `-0400-02-29` is a date). `days_from_civil`
  and `civil_from_days` are Howard Hinnant's algorithms over i64 days;
  `weekday(days)` (0 Sunday .. 6 Saturday), `day_of_year`, `is_leap_year`,
  `days_in_month` (0 outside 1..12), `civil_valid`. `civil_to_instant(c,
  offset_minutes)` and `instant_to_civil(i, offset_minutes)` convert through
  a fixed offset east of UTC below a day in magnitude (`InvalidOffset`
  otherwise); there are no time zones, only offsets.
- **RFC 3339** (RFC 3339 §5.6): `format_rfc3339(dst, instant,
  offset_minutes, fraction_digits)` writes
  `YYYY-MM-DDTHH:MM:SS[.f{n}](Z|±HH:MM)` with `Z` for offset 0, `n` in
  0..9 fraction digits truncated from the nanoseconds, and upper-case
  letters, returning the length (`rfc3339_size` tells it in advance).
  `parse_rfc3339(src): Result[Zoned, TimeError]` is strict about shape
  (exactly these separators and widths, one to nine fraction digits, nothing
  after the zone) and returns the UTC instant with the offset it was written
  in. Decisions: lower-case `t` and `z` are accepted on input as the RFC
  allows and never written; a leap second (`:60`) is `InvalidCivil` because
  the library cannot know when one occurred; `-00:00` is offset 0 (the
  "unknown offset" convention is not distinguished); the RFC's space
  separator note is not honored; a numeric offset must be `±HH:MM` with
  `HH < 24` and `MM < 60`, else `InvalidOffset`. Every `Instant` has a
  four-digit year, so nothing is unprintable.
- **Duration text** in Go's spelling: `format_duration(dst, d)` writes
  `0s`, `12ns`, `1.5µs`, `500ms`, `1h2m3.5s`, `-2562047h47m16.854775808s`
  exactly as Go's `Duration.String()` (at most `DURATION_TEXT_SIZE` bytes);
  `parse_duration(src)` accepts what Go's `ParseDuration` accepts (sign, one
  or more `<decimal>[.<decimal>]<unit>` terms with `ns us µs μs ms s m h`,
  `0` alone) and computes the fraction the way Go does, in `f64`, so the two
  agree bit for bit on every input, long fractions of an hour included.

`compiler/e2e_stdlib_time_test.go` checks the calendar (the epoch, leap
days across 1600/1900/2000/2100, years 0 and negative, the range ends,
weekdays and days of the year), civil conversions at several offsets, the
RFC 3339 spellings and thirty-one rejected shapes, Go's `RFC3339Nano` output at
random offsets, duration spellings and rejections, and every overflow edge,
with every expectation computed by Go's `time` package; each program runs
compiled and interpreted. A differential test formats 3000 random instants
at seven offsets and 1000 random durations in Oak, compares each line with
Go, parses it back, and parses 400 random duration spellings to Go's value.
`examples/time/time_test.oak` (`oak test examples/time`) states the round
trips as properties over the full i64 range.

- **Time sources** (the one sanctioned way to read time): a `TimeSource` is
  a record the consumer owns and passes by span, so who advances it is the
  environment's decision. `time_source_fixed(start)` never moves unless
  `time_source_set` steps the wall clock; `time_source_sim(start)` advances
  only through `time_source_advance(source, d)` (both clocks together, false
  and unchanged on a negative duration or an overflow), `time_source_set`
  and `time_source_shift_wall` (wall only); `time_source_native()` is
  unreadable until `time_source_refresh(source, wall_nanos, mono_nanos)` has
  run — reading it earlier traps, because a forgotten platform refresh is a
  bug the simulation cannot see. Every source carries the classic pair:
  `time_now(source)` is the wall clock (an `Instant`, free to jump) and
  `time_monotonic(source)` a `Duration` since creation that never decreases
  (a native host whose monotonic reading regresses is clamped). Deadlines
  are monotonic: `time_deadline(source, d)`, `time_expired(source,
  deadline)`, `time_remaining`, `time_elapsed`. Code written against a
  source — timeouts, leases, rate limiters, retries — is simulation-testable
  and fuzzable as it stands; `examples/timesim` is the worked consumer and
  `timesim` below drives it.

### Interval readings and attestation

A `TimeSource` may carry an attested error bound: `time_source_attest(source,
bound)` (a non-negative `Duration`, refused otherwise) is the platform
layer's statement of its synchronization error, or a scenario's decree;
`time_source_unattest` withdraws it. `time_interval(source)` is the
clock-ordered reading `Result[TimeInterval, TimeError]`: `[wall - bound,
wall + bound]` while attested, `Err(.Unattested)` otherwise, so a consumer
that orders events by time refuses rather than guesses.
`time_interval_before(a, b)` is definitely-before (`a.latest < b.earliest`;
overlapping intervals are unordered) and `time_interval_contains(i, at)`
membership. `Oak.TimeInterval` (`spec/lean/Oak/TimeInterval.lean`) proves
the reading contains the true time exactly when the clock's departure is
within the bound, that definitely-ordered honest intervals order their true
times the same way, and that an unattested source yields no ordering.

## `timesim`: simulated time with clock faults (`import("timesim")`)

`stdlib/timesim.oak` (a library package over `time` and `import(testing)`,
docs/spec/110-testing.md "Simulated time") is the environment side of a
`TimeSource` under deterministic simulation. `timesim_init(sim, faults,
tick_nanos)` makes a `TimeSim`; `timesim_advance(sim, source, d, choices,
data)` moves a simulated source by `d` and injects at most one fault drawn
from the choice tape (one roll in eight, uniformly among the enabled kinds;
a shrunk or exhausted tape injects nothing, so a shorter tape is a run with
fewer faults and strict replay reproduces them); `timesim_sync(sim, source,
clock, choices, data)` advances the source to the scheduler's `SimClock`
reading (ticks since the last sync times `tick_nanos`) so the event
timeline and the consumer's clock agree, faults included, and
`timesim_ticks(sim, d)` converts a duration back to ticks for scheduling.

The fault mask: `TIME_FAULT_JUMP_BACK` (1, the wall clock steps back up to a
day), `TIME_FAULT_JUMP_FORWARD` (2), `TIME_FAULT_STALL` (4, neither clock
advances this step), `TIME_FAULT_COARSE` (8, the wall clock is quantized to
`coarse_nanos`, 10 ms unless `timesim_set_coarse` says otherwise),
`TIME_FAULT_DRIFT` (16, the wall clock runs up to two percent fast or slow
against the monotonic one), `TIME_FAULT_BOUND_BREAK` (32, the wall clock is
stepped past the attested bound with the attestation left standing — the
interval reading lies, and `timesim_interval_honest(sim, source, interval)`
says so against `timesim_true_now`), `TIME_FAULT_UNATTEST` (64, the
attestation is withdrawn, so `time_interval` refuses), `TIME_FAULT_ALL`. The ledger (`jumps_back`,
`jumps_forward`, `stalls`, `coarsened`, `drifted`, `skew` — how far the wall
clock has departed from the monotonic timeline) is there to classify on.
The law every fault respects, asserted inside `timesim_advance`: **the
monotonic clock never decreases**; a consumer whose deadlines are monotonic
is unaffected by every fault but the stall, and the stall only delays.

Generators, each drawing a class first so the reducer moves toward the
simplest value: `timesim_instant` (near the epoch, at the range ends, on a
second or day boundary plus or minus a nanosecond, anywhere),
`timesim_duration` (zero, a nanosecond, up to a minute, up to a year, the
range ends, anywhere), `timesim_step(choices, data, max_millis)` (a
non-negative step), `timesim_offset_minutes` (zero, whole hours, the
extremes, anywhere in -1439..1439), `timesim_civil` (always valid; years 0,
-400, -1, the century rules, 1970, the instant range ends; days 1, the
month's last, February 28/29), and `timesim_rfc3339(dst, choices, data)`
(text for a generated instant, offset and fraction width, damaged one time
in four by a replaced byte or a truncation, for parser fuzzing). `Instant`
and `Duration` are records of one `i64`, so a typed command
(`derive.test_generate`) carries them through a carrier scalar — the
example's `Advance: u16` is whole milliseconds.

`examples/timesim` is the consumer that proves the point: a lease and a
one-shot timer written against `[*]time.TimeSource`, tested under a frozen
source (a wall step neither expires nor extends a lease), under every fault
mask (the monotonic clock never decreases; a client whose own deadline has
not passed can always renew; the timer never fires early, never twice, and
fires once its deadline has passed; clock faults and wall steps never move a
monotonic deadline; at most one client believes it holds the lease and the
server agrees with it), through the discrete-event simulator with client
crashes and restarts driving the source from `SimClock`, and as typed
command histories. `testrunner/timesim_example_test.go` runs it under the
Go suite; `.github/workflows/testing.yml` runs it with `oak test`.

## `timenative`: the operating system's clocks (`import("timenative")`)

`stdlib/timenative.oak` is the native realization of a `TimeSource`, and the
platform layer is the only code that imports it. `timenative_source(out)`
fills a refreshed native source; `timenative_refresh(source)` reads both
host clocks into it (false, unchanged, for a fixed or simulated source
handed to production code by mistake). The clocks are read in Oak through
the boundary: `clock_gettime` is an extern binding with `effects {
Os.Syscall }`, `CLOCK_REALTIME` and `CLOCK_MONOTONIC` are target constants
(`c.const`, `docs/spec/92-ffi.md` §2.11 — their values differ per host and
the C compiler, not Oak, resolves them), and the `struct timespec` the call
fills is a boundary struct passed through `c.out`. Nothing is linked but the
C library, which every POSIX.1-2001 host provides; that is the package's one
platform assumption, visible at build time. The earlier host-symbol shim
(`stdlib/native/oak_time_host.c`, `oak_time_host_*_nanos`) that stood in
while the FFI lacked out-pointers and target constants is gone.
`compiler/e2e_stdlib_timesim_test.go` checks the wall clock against Go's
within a minute, that the monotonic clock starts at zero and never decreases
over a thousand refreshes, and that a fixed source is refused.

## `objc`: the Objective-C runtime (`import("objc")`)

`stdlib/objc.oak` is Darwin-only and deliberately thin: `objc_class(name)`
resolves a class by its NUL-terminated name (`objc_getClass` over `c.cstr`)
and `objc_sel(name)` registers a selector (`sel_registerName`), both as
opaque `c.Ptr` values. Sending a message is the language form
`c.msg_send[(params) -> ret](receiver, selector, args...)` inside `unsafe`
(`docs/spec/92-ffi.md` §2.12): the bracketed signature is the sender's
assertion about the selector's implementation, checked at the call like an
extern signature, lowered to `objc_msgSend` cast to that prototype, and
recorded as the `OAK-B0122` assumption a strict module admits explicitly.
Nothing models Objective-C types, ownership, or dispatch beyond that; the
runtime's nil-receiver rule applies unchanged. A module that imports the
package declares the framework it drives (`framework Foundation`) in its
`oak.mod`, which brings the runtime library. arm64 only in this increment.
`compiler/e2e_ffi_objc_test.go` drives Foundation: `[[NSString alloc]
initWithUTF8String:"oak"]` has length 3, `[NSNumber numberWithInt:41]`
answers 41, and an `NSRange` boxed in an `NSValue` comes back by value.

## `arena`: reservations over an owner (`import("arena")`)

`stdlib/arena.oak` is bump allocation over an owner's element index space
(`docs/spec/92-ffi.md` §2.8.4): an `Arena { used, capacity }` hands out
offsets, never memory. `arena_reserve(a, count, align)` returns a
`Reservation { ok, offset, arena }`, the aligned start of a range that fits
after every earlier reservation and the arena after it, or `ok = false`
with the arena unchanged. `arena_align_up` rounds up without wrapping (an
offset that cannot be rounded becomes the largest `u32`, which no capacity
admits), and `arena_reset`/`arena_remaining` complete the surface. The
program carves the ranges with `subslice` over `view(&b)` or `span(&b)` of
a `Buffer[T]` or a fixed array, so the borrow checker decides what may be
live at once. Executed over a libc allocation in
`compiler/e2e_buffers_test.go`.

## `iosim` and `ionative`: the IO port (`import("io")`)

`docs/spec/120-io.md` fixes one completion-ring port two packages realize
with an identical exported surface. A program imports the port as `io`
and its manifest selects the realization — `replace io => iosim` for a
simulation build, `replace io => ionative` for the operating system — so
nothing in the program text changes (`compiler/e2e_io_port_test.go` is
one consumer under both).

- Storage is caller-owned and bounded: `IoRing`, `[N]IoRequest`,
  `[N]IoCompletion`, and one byte region every buffer is a `(base, len)`
  window into. `io_submit` returns false when the submission storage is
  full; `io_wait`/`io_poll` complete into the completion storage from
  index 0 and return the count (the storage must hold every pending
  request). Ops: `io_op_open`, `close`, `pread`, `pwrite`, `fsync`,
  `fdatasync`, `fsyncdir` (the directory's path bytes in the window);
  errors are the closed set `io_err_*` in `IoCompletion.error`, 0 for
  success. A request with `link` set must complete before the next one
  starts, and its failure cancels the rest of the chain (`io_err_canceled`).
- `iosim` is pure Oak over `SimDisk` (this module): a 64-block, 64-byte
  device holding up to 8 files of 512 bytes; bytes are packed into words,
  writes tear at block boundaries exactly as the device's mask allows,
  `io_wait` completes chains in a tape-chosen order, `io_poll` completes a
  tape-chosen subset. `io_attach(data, faults)` binds the run's tape and
  fault mask; `iosim_crash`/`iosim_restart` are the scenario's crash
  events (files close, unsynced bytes vanish, sizes revert);
  `iosim_trusted(slot)` says whether the durability contract applies to a
  file; `iosim_fault_count(kind)` reads the device's ledger; the
  submit/complete ledger (`iosim_ledger_*`) is the scenario's to forward to
  `testing_trace`. `testrunner/io_sim_test.go` runs a linked-fsync log
  through torn, dropped and lost-fsync faults and a crash.
- `ionative` is the portable backend of §5: bindings to
  `stdlib/native/oak_io_host.c` (`openat`, `close`, `pread`, `pwrite`,
  `fsync`, `fdatasync`, directory `fsync`), each declaring
  `effects { Os.Syscall }`; errno is mapped onto the port's errors in the
  shim and the raw code is readable through `ionative_last_errno`. Link
  the shim into any program that imports it. A `Sim` test package rejects
  it (undeclared externs), so the operating system cannot enter a
  simulation by mistake.
- `Oak.IoPort` (`spec/lean/Oak/IoPort.lean`) proves the contract's shape:
  a failed linked request cancels exactly the rest of its chain, a
  completed fsync covers every write completed before its submission and
  claims nothing else, and a read of a written range sees the write.

