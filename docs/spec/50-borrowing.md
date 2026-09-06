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

Initially, returning/storing a borrow beyond the lexical region that proves the owner lifetime is rejected.

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

The proof obligation is semantic range disjointness, not programmer assertion. If disjointness cannot be established, the operation is rejected in safe code or requires an explicit unsafe boundary.

## 7. Slicing

Slicing preserves access mode:

```text
owned array slice -> read-only view by default
view slice        -> read-only view
span slice        -> writable span
```

Obtaining writable access from owned storage is explicit (`span`, an equivalent borrow operation, or a mutable binding rule later specified).

Bounds must be proved statically or checked dynamically in safe code. Out-of-range access is never undefined behavior.

Exact index-normalization policy (including whether negative indices remain in Oak) is a separate sequence/indexing decision; it does not alter the ownership model.

## 8. Raw pointers

Raw pointers do not automatically participate in safe borrow tracking because arbitrary pointer arithmetic/aliasing can destroy provenance facts.

Creating/dereferencing/reinterpreting raw pointers therefore requires the relevant unsafe authority unless the compiler can prove a safe derived-pointer operation.

`unsafe` introduces assumptions; it does not disable unrelated typing/bounds/effect checks.

## 9. DMA and ownership states

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
