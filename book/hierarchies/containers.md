# Containers

Oak's container story is a three-axis hierarchy: **ownership × shape ×
capacity**. Every container sits at one coordinate, and the coordinate
determines its laws.

## Axis 1 — ownership

| Form | Meaning | Write authority |
| --- | --- | --- |
| `[N]T` | owned storage, length in the type | owner writes; borrows govern the rest |
| `[]T` | read-only view of an owner | none — a write through a view is a type error |
| `[*]T` | writable span of an owner | exclusive, or region-disjoint siblings (proven) |

Ownership is the load-bearing axis: the borrow checker's aliasing laws
(`docs/spec/50-borrowing.md`, proven in `Oak.Borrowing`/`Oak.Reborrow`)
are stated over it, and every element access — read or write — is
bounds-checked in the emitted C (`oak_index`, `oak_span_store_*`,
`oak_lv_idx`; executed trap tests in `compiler/e2e_test.go`).

## Axis 2 — shape

- **Products**: records (`Point: type = struct { x: i32, y: i32 }`) with
  declaration-order natural layout, proven (`Oak.RecordLayout`) and
  *cc-asserted in every artifact* (`sizeof`/`offsetof` static assertions).
- **Sums**: ADTs, matched with `?`, exhaustiveness-checked, lowered to
  tag-guarded C where payloads are read only under their tag
  (`Oak.ADTSemantics`). Generic sums monomorphize per instantiation
  (`Oak.Monomorphization`).
- **Vectors**: `simd.U8x16` and friends — 16-byte values with total lane
  semantics (`Oak.Simd`), NEON or portable lowering, one ABI.
- **Text**: `string = Str[Utf8]` — a validity-carrying view of bytes
  (`Oak.Utf8Validity`), phantom-indexed by encoding.

## Axis 3 — capacity

v1 has exactly one capacity discipline: **fixed at compile time**. `[N]T`,
`Ring[T, N]`, pools — capacity is a const parameter, storage is static or
stack, and there is no hidden allocation anywhere (a stdlib law inherited
from the Zig/TigerStyle lineage; see `docs/spec/60-effects-allocation.md`).
Growable containers are not a missing feature so much as a deferred
*policy*: they require the allocation-phase story, and kernels mostly
should not want them.

## Composition: the derived hierarchy

Coordinates compose. `Ring[T, N: u32]` = product shape × owned fixed
capacity, and its instantiation `Ring[u8, 8]` is a nominal type with a
proven layout (executed: `compiler/e2e_ring_test.go`). A pool
(`[N]Thread` + index links) is owned fixed capacity × product elements ×
the [intrusive doctrine](intrusive.md). Views/spans of any owned container
give the borrowed coordinate of the same shape — which is why `len`,
indexing, and the store helpers are uniform across the hierarchy: they are
axis-1 operations, indifferent to axis 2.

## What each coordinate refuses

The hierarchy is as much about exclusions as inclusions: views refuse
writes; owned aggregates refuse implicit moves (copies are explicit-cost,
`OAK-B0111` reserved for resource types); vectors refuse lane-type
punning without `simd`/`bits` operations; sums refuse field access
(match or nothing); and every container refuses unchecked indexing,
including through record-field paths (`pool[i].next` goes through the
checked lvalue helper). A container in Oak is precisely a shape plus the
set of refusals that keep it lawful.
