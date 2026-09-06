# Ownership and Borrowing

Oak's borrowing model is intentionally small: make common contiguous-memory ownership safe without requiring explicit lifetime syntax in ordinary code.

## 1. Core storage shapes

```oak
[N]T   // owned fixed-size array
[]T    // read-only borrowed view
[*]T   // writable borrowed span
*T     // raw pointer; unsafe authority
```

A view/span is non-owning. It identifies a contiguous region of another owner.

A conventional runtime representation for views/spans is pointer + length, but the semantic borrow rules do not depend on a particular field spelling.

## 2. Owner provenance

Every safe view/span has an owner/provenance relation established by construction.

Derived slicing does not create a new independent owner:

```text
OwnerOf(subslice(v)) = OwnerOf(v)
```

The compiler must not forget this relation merely because the derived value has its own pointer/length representation.

## 3. Borrow states

For one owner, the core abstract states are:

```text
Free
SharedRead(n), n > 0
UniqueWrite
```

Allowed creation transitions:

```text
Free          --view--> SharedRead(1)
SharedRead(n) --view--> SharedRead(n+1)
Free          --span--> UniqueWrite
```

Disallowed:

```text
SharedRead(_) --span--> error
UniqueWrite   --view--> error
UniqueWrite   --span--> error
```

Releasing the last shared reader returns to `Free`; releasing the unique writer returns to `Free`.

## 4. Lexical v1 lifetimes

The first safe implementation may conservatively keep a borrow live until the end of its lexical block.

This is intentionally simpler than general lifetime inference and is sound when borrows cannot escape their owner scope.

The compiler may later shorten borrows using liveness/NLL-style analysis without changing program meaning, because that is an acceptance optimization over the same ownership rules.

## 5. Escape

A borrowed value may not outlive its owner.

Initially, returning/storing a borrow beyond the lexical region that proves the owner lifetime is rejected. The compiler enforces this conservatively today by rejecting any function signature whose return type is a view or span (`OAK-B0109`). `Oak.Escape` proves the discipline: dropping scope-local borrows on exit preserves owner liveness, an escaping borrow of a scope-local owner dangles, and an escape of a strictly longer-lived owner would be safe — the headroom the region-indexed forms below can claim without changing the ownership model.

Future region-indexed forms can make escape explicit:

```oak
Arena[R]
View[T, R]
Span[T, R]
```

or equivalent compiler-internal regions, but ordinary code should not require manual lifetime punctuation when the relation is inferable.

## 6. Disjoint mutable regions

The conservative rule treats two writable regions of one owner as conflicting.

Oak may admit simultaneous mutable subspans when the compiler proves their byte/element ranges are disjoint.

The proof obligation is semantic range disjointness, not programmer assertion. If disjointness cannot be established, the operation is rejected in safe code or requires an explicit unsafe boundary. Inside an unsafe boundary the admission is recorded as an auditable assumption (`OAK-B0110`, warning severity) rather than silently dropped; every unrelated borrow invariant remains checked (`Oak.Unsafe`).

## 7. Slicing

Slicing preserves access mode:

```text
owned array slice -> read-only view by default
view slice        -> read-only view
span slice        -> writable span
```

Obtaining writable access from owned storage is explicit (`span`, an equivalent borrow operation, or a mutable binding rule later specified).

A derived writable span is a **reborrow**. While any child span is live, direct use of its parent span is suspended. When the last live child leaves its lexical scope, the parent becomes usable again. This preserves usable writable authority along a parent/child chain without requiring lifetime syntax in ordinary Oak code.

Sibling writable reborrows of one parent span may coexist when the compiler statically proves their regions pairwise disjoint (the disjoint-mutable-regions rule of section 6 applied to derived spans). This admits splitting one span into independent writable halves without an unsafe boundary. A reborrow whose region cannot be established, or that cannot be proven disjoint from every live sibling, is rejected; an unknown-region reborrow therefore admits no siblings in either direction.

Known slice/subslice bounds are translated into the same absolute owner coordinate space as their parent region. If the compiler cannot establish a precise derived region, it keeps the region unknown and fails closed for alias-disjointness decisions rather than inventing precision.

Bounds must be proved statically or checked dynamically in safe code. Out-of-range access is never undefined behavior. This is enforced in the C backend: view/span indexing lowers to trapping bounds-checked helpers, owned-array indexing to a static-length guard, and unknown containers fail closed at compile time. Stores are symmetric: `s[i] = value` writes through spans and owners via bounds-checked trapping stores, and writing through a read-only view is rejected by the type checker.

Exact index-normalization policy (including whether negative indices remain in Oak) is a separate sequence/indexing decision; it does not alter the ownership model.

## 8. Move/consume

Owned aggregates (`[N]T` and resolved records) have explicit value semantics
in v1: binding or passing one is an explicit-cost copy, never a hidden
allocation and never an ownership transfer, so use-after-move cannot occur
yet. Move/consume semantics — and their diagnostics, for which `OAK-B0111`
is reserved — arrive together with resource types (handles, arenas, files),
whose values must not be duplicated. When they land, the diagnostic must
show both the move site and the later use (`15-diagnostics` section 6).

## 9. Raw pointers

Raw pointers do not automatically participate in safe borrow tracking because arbitrary pointer arithmetic/aliasing can destroy provenance facts.

Creating/dereferencing/reinterpreting raw pointers therefore requires the relevant unsafe authority unless the compiler can prove a safe derived-pointer operation.

`unsafe` introduces assumptions; it does not disable unrelated typing/bounds/effect checks.

## 10. DMA and ownership states

The same ownership vocabulary should extend to machine/device custody without special pointer syntax.

Conceptually:

```text
Buffer[CpuOwned]
    --submit--> Buffer[DeviceOwned]
    --complete--> Buffer[CpuOwned]
```

CPU code cannot safely access a device-owned buffer because it lacks the corresponding authority/state, not because the pointer has disappeared.

This is a protocol/typestate refinement layered on the core borrow model.

## 10. Strings and wrappers

A type containing a view/span inherits its borrow lifetime. Wrapping `[]u8` in `Str[Utf8]` does not sever provenance or extend lifetime.

No special string escape rule is needed if semantic wrappers preserve ownership facts.

## 11. Formal verification targets

The core borrow state machine must prove:

- no state contains simultaneous read and write authority;
- at most one unique writer exists;
- creating a span succeeds only from `Free`;
- creating a view never produces write authority;
- release cannot underflow a reader count;
- derived views/spans preserve owner provenance;
- safe borrow values cannot outlive owners;
- disjoint mutable borrowing, when enabled, relies on proved disjoint ranges.

`spec/lean/Oak/Borrowing.lean` models the local borrow-state laws. Temporal ownership transfer across asynchronous actors may additionally use TLA+ when introduced.
