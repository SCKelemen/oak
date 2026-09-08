# Oak collection ports

These implementations live in Oak source and are included by `import(std)`.
The host Go code only embeds the source. All storage is supplied by the caller;
the libraries allocate nothing and provide no synchronization.

## Filters

`BloomConfig { cells, probes, seed, blocked }` selects ordinary Bloom
(`blocked: false`) or 512-bit blocked Bloom (`blocked: true`). Cells must be
positive; probes must be 1..64. Blocked configurations require a multiple of 512
cells. Keep configuration unchanged while storage contains entries.

- `bloom_insert`, `bloom_query`, `bloom_clear` use byte-packed bits.
- `counting_bloom_update(storage, config, hash, insert)` and
  `counting_bloom_query` use one u8 counter per cell. Repeated probe locations
  are counted once. Counter overflow/underflow is checked before any mutation.
- Queries return `Result[Bool, FilterError]`: false means definitely absent;
  true means possibly present. Configuration/storage errors are distinct.
- Removal requires proof of a successful unmatched insertion. A positive query
  is insufficient, since it can be a false positive.
- Inputs are caller-computed u64 key hashes. Hash collisions contribute to
  false positives. The deterministic mixer is not cryptographic.
- Zero-initialize active storage. Padding and spare bytes are preserved.
  Clear counters explicitly before reusing them with another configuration.
- The mixer and probe sequence match the OS Zig Bloom implementations.
  u64 arithmetic relies on the current backend's unsigned modulo arithmetic.

## Hash maps and sets

`hash_table_put[T]`, `hash_table_find[T]`, `hash_table_remove[T]`,
`hash_table_count[T]`, and `hash_table_clear[T]` operate on caller-owned slot
arrays. A slot has `key: u64`, reserved `state: u8`, and any inline value fields:

```oak
Entry: type = struct { key: u64, state: u8, value: u32 }
```

This is an exact u64-key map, not an arbitrary-key comparator API. State is
0 empty, 1 occupied, 2 tombstone; begin with zeroed slots. Do not modify live
keys/state except through the API. Keep storage and capacity fixed while active.
Put normalizes the incoming state and returns Ok(true) for insertion, Ok(false)
for replacement, or Err(Full) without mutation. Find returns an optional slot
index; read the payload through the same view. Indices are not stable handles
across remove, clear, or reuse. Removal and clear leave stale payload bytes.

Linear probing is bounded by capacity, remembers tombstones, and continues
searching for an existing key before reusing one. Full-table replacement works.
Count scans the array; there is no hidden cursor, allocation, resize or rehash.
Worst-case operations are linear in capacity. Rebuild externally when tombstones
or high load degrade lookup performance.

`HashSetSlot` plus `hash_set_insert/contains/remove` provides an exact u64 set.
Use the generic count/clear functions for sets too.

## Bits and flags

`bitset_combine` supports Union, Intersection, Difference and SymmetricDifference.
Both arrays must cover the same logical bit count. It preflights lengths and
preserves destination padding/spare bytes. `bitset_find_next` finds the next set
or clear bit at/after a start index, returning None beyond the logical domain.
Normal Oak borrow rules apply to the mutable destination and immutable source.

`FlagBits { bits, allowed }` supports validated construction/update and all/any
membership. Unknown mask bits are rejected. It is a runtime u64 mask domain,
not compile-time separation of two flag types with the same representation.
Use domain-specific wrapper records to express that distinction. Treat fields
as private by convention and construct values with `flags_create`.

## Remaining parity with SCKelemen/os

Already present before this port: array lists, rings, deques, indexed intrusive
singly/doubly linked lists, queues, min heaps, basic bitsets, and bitmap ID pools.

This batch adds the filter/map/bit foundations above. Still to port:
cuckoo, quotient and counting quotient filters; static XOR/fuse filters;
generational freelists/slabs; skip lists; tries; balanced and intrusive trees;
interval trees; debug event rings, per-CPU adapters and wire encoding; and the
OS assertion contracts beyond Oak's existing assert builtin. Pointer-intrusive
structures also need an explicit Oak borrowing/ownership design. The OS still
contains Zig infrastructure; this batch does not convert kernel call sites.

Native tests in `compiler/e2e_oak_libraries_test.go` check exact filter bytes,
counting probe deduplication and saturation, collision-heavy map traces against
a Go map, flag validation, bitset padding, and emitted allocator-free C.
Run `go test ./compiler -run '^TestE2EOakLibraries' -count=1`.
