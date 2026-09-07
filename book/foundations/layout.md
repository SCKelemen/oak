# Layout: Alignment, Packing, and Cache Geometry

Every record in Oak has a *proven* layout: the compiler computes the
placement, a Lean theorem establishes its laws, and the emitted C carries
compile-time assertions on `sizeof`, every field's `offsetof`, and (for
declared layouts) `_Alignof` — so the C compiler itself ratifies the
claim in every artifact. A layout the compiler cannot place fails closed;
nothing is ever guessed. This chapter is about the two knobs on that
machinery and when systems code needs them.

## The default: natural ordered layout

Fields stay in declaration order; each begins at the next address
divisible by its alignment; the record's alignment is its largest field's;
the size rounds up to that. This is the layout C programmers reason about,
minus the reordering temptation — **declaration order is authoritative**,
so the padding you see in the source is the padding you get, and putting
your `u8`s together is a decision you make, not one a compiler makes
behind your back.

## The two knobs

No attribute grime, no `#[repr(C, packed, align(64))]` floating above the
declaration — the layout spec is a parenthesized clause on `struct`, in
the same voice as `Ring[T, N: u32]`:

```oak
Wire: type = struct(packed) {     // wire formats, hardware registers
  magic: u32
  kind: u8
  length: u16                     // offset 5; sizeof == 7, not 8
}

Line: type = struct(align: 64) {  // cache-line ownership
  cell: Atomic[u32]               // sizeof == 64, alignof == 64
}
```

`packed` places fields densely — each begins exactly where the previous
ended, proven contiguous and exactly sum-of-sizes
(`Oak.LayoutSpec.placePacked_dense`, `packed_cursor_exact`). `align: N`
raises the record's alignment without moving a single field (placement is
the natural placement *by definition*; only tail padding changes). Both
combine: `struct(packed, align: 4)`. Both carry through generic
templates to every instantiation.

Two things are rejected rather than approximated:

- **Under-alignment.** `align: N` below the natural alignment is an
  error. Lowering alignment without removing padding means nothing;
  packing is the way down.
- **Atomics in packed records.** Dense placement can land an `Atomic[T]`
  cell unaligned, and misaligned C11 `_Atomic` access is undefined
  behavior and never lock-free. The checker rejects it; the backend
  fails closed independently.

## When you want packed: the boundary layer

Packed layout is for bytes that leave the machine or arrive from
hardware: network headers, on-disk formats, descriptor tables, MMIO
register blocks. The doctrine is to keep packed types at the *boundary*:
parse a packed `Wire` into a natural record once, work on the natural
form, and serialize back once. Packed records nest in natural ones
through the ordinary representation machinery — a `crc: u8` after a
7-byte packed header sits at offset 7, and the emitted C asserts it —
so a framing struct around a wire header costs nothing.

## When you want align: cache geometry and false sharing

Two atomics that live on the same 64-byte cache line are *physically*
shared even when they are *logically* independent: every CAS or store on
one evicts the line under the other core's feet. This is **false
sharing**, and it is the classic silent 10× on every queue in the
[catalog](../structures/catalog.md) — the SPSC ring's `head` and `tail`
are written by different cores by design, and placing them adjacent
undoes the whole point of the algorithm.

The cure is one aligned wrapper record, and the phantom habit applies —
name what the line is for:

```oak
Cursor: type = struct(align: 64) {
  cell: Atomic[u32]
}

head: Cursor    // consumer's line
tail: Cursor    // producer's line
```

Each cursor now owns its line: `sizeof(Cursor) == 64` means even an array
of them never shares, and `_Alignof == 64` is asserted in the emitted C,
not hoped for. This is the layout-level half of the doctrine the
[CSP chapter](../concurrency/csp-models.md) states protocol-level:
*reduce sharing until what remains is deliberate* — memory orders make
the sharing correct, cache geometry makes the non-sharing real.

## The ladder coordinates

Layout specs are representation policy, not semantics: a packed `Wire`
and a natural record with the same fields are different *storage*, same
*meaning*. That separation is why the proofs compose — the semantic
record laws (order, uniqueness, lookup) hold regardless of placement, and
the placement laws (density, alignment, non-overlap, exact size) hold
regardless of meaning. The claims here are **executed**
(`TestE2EPackedWire`, `TestE2EAlignedCacheLine`,
`TestE2ELayoutSpecOnTemplate`) and **proven** (`Oak.LayoutSpec`,
`Oak.RecordLayout`), with the C compiler as the standing witness.
