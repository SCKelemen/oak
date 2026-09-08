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

Temporary writable exclusivity is not consumption. A `UniqueWrite` borrow suspends other access and eventually returns authority to the owner. Consumption permanently invalidates the consumed resource value and the aliases whose authority depends on it.

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

## 8. Symbolic extents

A view/span already carries a runtime length. Oak may additionally attach a compile-time **extent proposition** to that value without changing its runtime representation.

Conceptually:

```text
Extent(xs) = N
```

where `N` may be a constant, a compile-time value parameter, or a fresh symbolic extent inferred from program structure.

This is deliberately different from `[N]T`. An owned `[N]T` has representation-bearing fixed size and `N` participates in layout. A borrowed `[]T` or `[*]T` remains pointer + length (subject to target representation); its symbolic extent is a proposition about that value, not a new allocation shape.

Extent propositions may be introduced and propagated by operations whose semantics establish them. Examples include:

```text
Extent(view(array[N])) = N
Extent(slice(xs, a, b)) = b - a        when the bounds are established
Extent(left) + Extent(right) = Extent(parent)  for a proved split
```

A function may require relationships between extents without requiring dependent runtime representation. Surface syntax is not yet frozen; conceptually a same-length operation can require:

```oak
fn dot[N](a: []f32 where len = N, b: []f32 where len = N): f32
```

When an operation returns a length that cannot be expressed using caller-visible symbols, the semantic result may introduce a fresh existential extent:

```text
exists N. []T where Extent(result) = N
```

The compiler may keep such existential extents internal until Oak has surface syntax that improves ordinary code.

The initial extent theory should remain intentionally small and decidable. Equality, constants, addition/subtraction, inequalities, and multiplication by known constants are sufficient starting points. Oak does not require general dependent typing to obtain useful size facts.

Extent facts may discharge bounds checks, establish same-shape preconditions, and strengthen disjoint-region proofs. Failure to prove an extent relationship must fail closed; the compiler must not guess from runtime coincidence.

## 9. Move/consume and resource flow

Owned aggregates (`[N]T` and resolved records) retain explicit value semantics in v1: binding or passing one is an explicit-cost copy, never a hidden allocation and never an ownership transfer.

Resource types — handles with unique custody, arenas, files, device submissions, or other non-duplicable values — add a distinct **consumption** operation. Consumption is a semantic flow fact, not a spelling of ordinary mutable borrowing and not necessarily a distinct nominal type constructor.

Conceptually, a parameter or operation may consume a resource:

```oak
fn close(file: consume File): ()
fn submit(buffer: consume Buffer[CpuOwned]): Buffer[DeviceOwned]
```

Exact surface syntax is not frozen. The normative semantics are:

- after a value is consumed, that value cannot be used again;
- any alias whose authority depends on the consumed value is also invalid for later resource access;
- a resource cannot be consumed while an incompatible live borrow depends on it;
- consuming an input and proving that an output is alias-free are separate facts;
- consumption does not imply allocation, copying, or destruction unless the operation separately specifies those effects;
- safe control flow must establish that every reachable use occurs before consumption or on a path where consumption did not occur.

The checker should track alias classes or equivalent provenance so that consumption invalidates the relevant authority rather than merely one variable name. Copyable values remain outside this rule unless their type/protocol explicitly opts into resource semantics.

`OAK-B0111` is reserved for use after consumption. Its diagnostic must show the consume site, the later use, and any relevant alias/provenance chain that explains why the later name lost authority (`15-diagnostics` section 6).

## 10. Raw pointers

Raw pointers do not automatically participate in safe borrow tracking because arbitrary pointer arithmetic/aliasing can destroy provenance facts.

Creating/dereferencing/reinterpreting raw pointers therefore requires the relevant unsafe authority unless the compiler can prove a safe derived-pointer operation.

`unsafe` introduces assumptions; it does not disable unrelated typing/bounds/effect checks.

## 11. DMA and ownership states

The same ownership vocabulary should extend to machine/device custody without special pointer syntax.

Conceptually:

```text
Buffer[CpuOwned]
    --consume/submit--> Buffer[DeviceOwned]
    --consume/complete--> Buffer[CpuOwned]
```

CPU code cannot safely access a device-owned buffer because it lacks the corresponding authority/state, not because the pointer has disappeared.

These transitions combine protocol/typestate refinement with consumption: the previous state value is invalid after transfer, while the returned value carries the new custody state.

## 12. Strings and wrappers

A type containing a view/span inherits its borrow lifetime. Wrapping `[]u8` in `Str[Utf8]` does not sever provenance or extend lifetime.

No special string escape rule is needed if semantic wrappers preserve ownership facts.

The bootstrap return check recursively rejects views/spans stored in resolved
records, fixed arrays, unions, and intersections with `OAK-B0109`. Owning the
outer container does not give it ownership of storage referenced by an element.
The check also follows nominal and generic ADT payloads. Phantom type
parameters do not count as stored borrows; GADT variants are considered
conservatively even if index equations might make them unreachable. Recursive
ADTs are analyzed using finite borrow-presence states for their type arguments.

Until field-sensitive provenance and destination lifetimes are represented,
aggregate initializers, parameters, arguments, assignments, and field/element
writes containing borrowed storage are rejected with `OAK-B0109`. This is a
conservative restriction, not support for storing safe aggregate borrows. Direct
views/spans of borrow-free elements, owned records/ADTs, and direct literal strings
remain supported. String fields/payloads count as borrowed storage, even when an
individual initializer is a literal. Typechecking retains resolved local expression/declaration
types so this boundary cannot depend on a local scope remaining in the global
environment.

Scoped UTF-8 construction is available through `str_from_utf8`, with `str_bytes`
providing the inverse read-only view. Both propagate the source owner/region into
an explicit new binding. Direct borrowed parameters receive caller-owned origins;
view/string aliases retain shared reads and span aliases suspend their parent.
Borrowed bindings cannot be reassigned, and string declarations require a tracked
initializer. Direct literal-string returns are allowed; borrowed returns and
general region-aware wrapper storage remain unavailable. Function literals in an
active borrow scope are conservatively rejected pending capture-lifetime analysis.

## 13. Formal verification targets

The core borrow/resource model must prove:

- no state contains simultaneous read and write authority;
- at most one unique writer exists;
- creating a span succeeds only from `Free`;
- creating a view never produces write authority;
- release cannot underflow a reader count;
- derived views/spans preserve owner provenance;
- safe borrow values cannot outlive owners;
- disjoint mutable borrowing, when enabled, relies on proved disjoint ranges;
- consumption permanently removes the consumed resource authority on that control-flow path;
- live aliases in the consumed alias class cannot retain resource authority;
- temporary `UniqueWrite` borrowing and permanent consumption remain distinct transitions;
- extent propagation preserves the semantic length equations introduced by array views, slices, and proved splits.

`spec/lean/Oak/Borrowing.lean` models the local borrow-state laws. Consumption/alias-class and symbolic-extent lemmas should extend that proof surface as the checker representation lands. Temporal ownership transfer across asynchronous actors may additionally use TLA+ when introduced.


