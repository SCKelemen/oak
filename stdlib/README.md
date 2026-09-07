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

The initial argument set is fixed-width integers, Bool and concrete named types.
Const parameters on functions, composite type arguments, inferred generic calls,
generic methods, and first-class generic function values are not implemented.
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

## Verification and remaining work

`compiler/e2e_stdlib_test.go` compiles real imported Oak through the compiler and
system C compiler and executes the result. It covers typed outcomes, independent
ring instances, wraparound, capacity one, full/empty behavior, byte-copy failure,
explicit specialization and negative compilation cases. Seeded traces compare
128 operations at capacities 1, 3 and 8 against a plain sequence model; invalid
cursor fields must trap. Endian tests compare all six width/order pairs against
Go byte-encoding fixtures, including high-bit and maximum values at unaligned
offsets. Bitset traces check each backing byte against a reference model across
zero, partial-byte and byte-boundary capacities; bounds tests cover unchanged
failed writes and maximum u32 arguments.

The standard-library workflow runs the full Go suite with the race detector. These are implementation tests, not formal refinement proofs. Native
Apple Silicon execution, PAC/tag representations, capability transfer/revocation,
pools/intrusive structures, concurrent rings, broader collections and persistence
protocols remain separate work; importing this module does not implement them.
