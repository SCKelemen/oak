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

Initially, returning/storing a borrow beyond the lexical region that proves the owner lifetime is rejected. The compiler enforces this conservatively by rejecting any function signature whose return type is a view or span (`OAK-B0109`), except the region-indexed signatures of section 8c, whose returned view is proven to borrow a parameter's owner. `Oak.Escape` proves the discipline: dropping scope-local borrows on exit preserves owner liveness, an escaping borrow of a scope-local owner dangles, and an escape of a strictly longer-lived owner would be safe — the headroom the region-indexed forms below can claim without changing the ownership model.

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

## 8b. Borrows inside aggregates (implemented subset)

A record whose fields hold views or spans is itself a borrow. The first
increment admits exactly the lexical case the escape rule can already prove:

- A **local binding** of such a record type, initialized from a record
  literal whose borrow-carrying fields are each `view(&owner)` or
  `span(&owner)` of an owner in scope, a tracked read-only view binding (a
  local view or a view parameter), or a nested record literal of the same
  shape — or initialized as a copy of a binding admitted this way.
- The binding then **borrows every such owner**, one borrow per field path
  (`cursor.data`), with the same kind, region, and block depth a direct
  `view`/`span` binding would have: the owner cannot be written while a view
  field lives, a span field is exclusive, and the borrows end with the block.
- Every escape rule keeps the record in place: it is not returned, stored
  into an aggregate or global, reassigned, or passed to a function, and its
  borrow fields are not reassigned (`OAK-B0109` in each case). Its fields may
  be read and indexed (with the ordinary bounds check), and a view field may
  itself be passed on as a view.
- A span field taken from an existing span *binding* is not admitted (it
  would be a second exclusive path); take it from the owner directly.

In the C backend a view or span field is the `{base, len}` struct the views
already lower to, placed by the natural layout with the emitted `offsetof`
and `sizeof` assertions. The interpreter stores the view object in the
record. Views in records that cross a call, are returned, or live in
storage remain the field-sensitive provenance work of
`roadmap-authority-resources.md` milestone 4 (e).

## 8c. Region-indexed borrowed returns (implemented)

Section 5's conservative rule rejects every function whose return type is
a view or span (`OAK-B0109`). Section 8b lets a record hold views, but only
inside the function that built it. Together they mean a zero-copy cursor
over a frame can exist but cannot be *handed back*: a decoder that finds a
record inside a buffer must copy it out or return indices for the caller
to re-index. The storage-engine evaluation named this first among the
features it needs, and the codecs spec lists borrowed decoded views as its
own pending relaxation of the same rule. This section is the normative text; the
"Increments" list at its end records what is implemented.

### What the proof already allows

`Oak.Escape` models scopes by lexical depth and proves two things about an
escaping borrow: `escape_local_owner_dangles` — a borrow whose owner lives
in the exiting scope cannot survive it — and
`escape_outer_owner_preserves_wf` — a borrow of a strictly longer-lived
owner may leave the scope rebound at the enclosing depth, and every
invariant holds. A function's parameters are exactly the owners that
outlive its body. A returned borrow whose provenance is a parameter is the
second theorem; a returned borrow of a local is the first. The rule below
is that distinction made syntactic, and nothing else changes in the
ownership model.

### Signatures

A borrowed return names the parameter region it borrows from. The
region is a type parameter written where type parameters go, and views and
spans take it as a second argument. Regions are **erased** before type
checking (`typechecker/regions.go`): a type parameter that occurs only in
region positions leaves the declaration, `View[T, R]` becomes `[]T`,
`Span[T, R]` becomes `[*]T`, and a region argument to a region-carrying
record is dropped; the structure is kept for the borrow checker. Nothing
at run time depends on a region, and a region-parameterized function is not
a template — it has one body and one C definition.

```oak
frame[R]: (buf: View[u8, R], at: u32): View[u8, R]
tail[R]: (buf: Span[u8, R], from: u32): Span[u8, R]
```

`[]T` and `[*]T` stay the ordinary spellings and mean "a fresh region no
one else names". A signature that returns a view or span **elides** the
region when exactly one parameter is a view, span, or record carrying a
region of a matching element type: the return borrows from it.

```oak
frame: (buf: []u8, at: u32): []u8          // elided: borrows buf
split: (a: []u8, b: []u8): []u8            // rejected: name the region
```

Two or more candidate parameters, or none, require the explicit form.
The same elision holds for spans: a `[*]T` return with exactly one `[*]T`
parameter of that element type. Nothing is inferred from the body; the
signature is the contract the caller sees, and the body is checked against
it. A region names exactly one parameter; a view result cannot come from a
span region (that would place a read-only borrow beside a writable one on
one owner), and a span result cannot come from a view region.

### The callee's obligation

The returned expression must be a borrow whose provenance is the named
region: the parameter itself, a `subslice`/`v[lo:hi]` of it, a view field
of a record parameter carrying `R`, or a view of the same provenance
threaded through a local binding. Returning a borrow of a local owner, a
borrow of a different parameter, or a borrow of unknown provenance is a
new diagnostic, `OAK-B0113` (returned borrow escapes its declared region),
with the provenance chain in the message as the other borrow diagnostics
do. `OAK-B0109` remains for signatures with no region at all — a view
return in a function with no candidate parameter has nothing to borrow
from and is rejected as today.

A span return is exclusive: while the result is live at the caller, the
argument's owner is suspended as by a reborrow (section 7). A view return
keeps the owner readable and unwritable.

### The caller's obligation

At a call whose return is region-indexed, the result is a **reborrow of
the argument** passed in that region's position: same owner, same kind
(view or span), and the argument's region when the callee's return is the
whole parameter or a subslice with folded bounds; otherwise the region is
unknown and fails closed for disjointness decisions (section 7). It is
bound at the caller's block depth and ends with the block, like any local
borrow. Storing it in a global, returning it from a function without a
matching region, or letting it outlive the argument's owner are the
existing rules applied to a borrow the checker already knows how to
track.

### Records carrying regions

A record type may take a region parameter and use it in its view and span
fields:

```oak
Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
open: (buf: []u8): Cursor[R]               // elided: R is buf's region
advance: (c: Cursor[R], n: u32): Cursor[R]
```

Such a record is a borrow of `R`'s owner (section 8b) and now may be
passed to and returned from functions whose signatures carry the same
region, with the caller-side rule above applied per view field. `Cursor`
without a region argument is the section 8b local form: it cannot cross a
call. Storing a region-carrying record into a global or into a record
without the region stays rejected: there is no static region.

### Interpreter and backend

Nothing changes at run time. A view or span is the `{base, len}` pair it
is today, and a region is erased like a phantom type parameter. The
interpreter's view object already carries its owner; the backend's
`oak_view_T` already carries the base. The work is entirely in the borrow
checker's provenance tracking across the call boundary and in the
signature grammar.

### Proof obligations

`Oak.Escape` gains region labels: a live borrow records the region it was
drawn from, a function boundary is a scope whose parameters are the
outer-depth owners, and the theorem the rule instantiates is
`escape_outer_owner_preserves_wf` applied to a borrow whose region is a
parameter's. The new lemma is that the caller-side reborrow is
well-formed whenever the argument's borrow was: the result is bound no
deeper than the caller's scope and its owner is the argument's owner.
Subslices carry the region-coordinate translation of section 7 unchanged.

### Increments

All three increments below are implemented; the list records the order
they landed and the shape each admits.

1. Elided single-candidate view returns: a `[]T` return
   with exactly one `[]T` parameter of the same element type (variadic
   functions excluded — the bundled view is call-lifetime storage). The
   callee's result must trace to that parameter — the parameter, a local
   bound from it, `subslice`/`view_as` of one, a slice expression over one,
   a conditional whose arms all trace to it, or another region-indexed call
   through its region argument — or `OAK-B0113` names what it borrows
   instead. At the caller, a binding initialized from such a call is a
   read-only reborrow of the region argument (a tracked view binding,
   `view(&owner)`, a subslice or slice of one, or a nested region-indexed
   call; a span argument or an untraceable one is `OAK-B0113`), bound at
   the caller's block depth with an unknown region. Signatures with two
   candidates or none keep `OAK-B0109`. `Oak.Escape.return_param_borrow_wf`
   is the callee's theorem and `Oak.Escape.reborrow_wf` the caller's.
   Executed in both realizations (`compiler/e2e_borrowed_returns_test.go`).
2. Explicit `[R]` regions on functions with the `View[T, R]`/`Span[T, R]`
   spellings, choosing among several candidate parameters
   (`pick[R]: (a: View[u8, R], b: []u8): View[u8, R]`); span returns, elided
   or explicit, whose result at the caller is a reborrow of the argument
   span — the argument is suspended while the result lives (`OAK-B0107`)
   and usable again when it leaves scope. Signature validation is
   `OAK-B0113`: a return region naming no parameter, or two, or a view
   result from a span region. Executed: `compiler/e2e_region_returns_test.go`.
3. Region-carrying records (`Cursor[R]: type = struct { data: View[u8, R],
   pos: u32 }`, exactly one region per record): a function whose signature
   gives a record parameter a region receives its borrow fields as borrows
   (`c.data`) and may pass them on, subslice them, or build and return a
   record in the same region; a returned record's borrow fields are traced
   like any result, and at the caller each field of the bound result is a
   reborrow of the region argument's sources of that field's kind. A
   section 8b local record whose borrows are tracked may be passed to a
   region-declared parameter; a record parameter without a region keeps
   `OAK-B0109`. Executed: a cursor opened, advanced through nested calls,
   and read, with the owner write while it lives rejected.
4. ADT payloads and match bindings. A region may be carried by an ADT
   whose payloads hold borrows — `Result[Frame[R], E]`,
   `Option[View[u8, R]]` — in parameters and returns alike. Borrowed
   storage is named by **path**: record fields by name, a variant's payload
   as `$Variant` (`r.$Ok.payload`), so the bound result of a call reborrows
   the region argument once per path, and a match arm's payload binding
   (`r ? | .Ok(f) => ...`) reborrows the scrutinee's paths under that
   variant for the arm only — `f.payload` is a borrow inside the arm, and
   the owner is writable again after the match (the `Result` binding
   itself stays lexical). A returned variant traces its payload; a bare
   variant carries nothing. Provenance is traced statically when the
   lexical borrows have already dropped: a value assembled inside nested
   conditionals is followed through the locals' declarations, record
   literals, and payload bindings back to the region's owners, always as
   a superset of what the value can hold, so the trace can only reject
   more. Strings and unions of borrows are outside the path form and fail
   closed. This is what a derived decoder needs to hand back views
   (`71-codecs.md` §13a); executed there in both realizations.

What stays rejected: borrows in globals and statics, borrows in records
without a region crossing a call, a returned borrow whose provenance the
checker cannot establish, a region naming more than one parameter, a record
with more than one region, region functions called across package
boundaries by qualified name, and any borrow outliving its owner.

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

Resource callable metadata may additionally classify parameters as shared-borrowed,
mutable-borrowed, or consumed without freezing source syntax. These modes impose a
call-local alias compatibility rule over explicitly mode-marked resource arguments:

- two shared-borrowed arguments may identify the same resource authority class;
- if either marked argument is mutable-borrowed or consumed, those two arguments
  must identify distinct resource authority classes;
- mutable-borrowed exclusivity ends when the call ends and does not consume the
  caller's resource authority;
- a consuming parameter invalidates its authority class only after the call has
  passed all call-local authority checks;
- a call rejected because marked arguments alias has not occurred semantically,
  so it must not consume any argument or cause derivative use-after-consume errors.

This rule is defined over resource provenance/alias classes rather than variable
spelling: passing two different names for one authority is still an alias conflict.
Unmarked resource parameters retain their ordinary semantics until a semantic or
ABI contract explicitly assigns an authority mode. `OAK-B0112` reports violations
of this call-local exclusivity rule.

The executable model normalizes consumed modes and legacy consumption metadata to
one contract. Conflicting metadata is rejected. A successfully checked call whose
contract establishes fresh result authority may be passed directly as a resource
argument; naming that result first does not change its exclusivity semantics.
Rejected calls do not establish fresh results. Valid nested-call effects are not
rolled back when a surrounding call is rejected.

**Reassignment** of a resource binding is tracked by provenance rather than
rejected: `alias = h` makes `alias` denote `h`'s authority from that point,
so a later exclusive pairing of the two names is an alias conflict and
consuming through either consumes both; `h = open(..)` from an operation
that returns fresh authority gives `h` a new live class and revives no old
alias of the class it left; any other resource-valued right-hand side gives
the name unknown provenance, and later exclusive or consuming use of it
fails closed. The class a name leaves keeps its state and its other
aliases. A rebound parameter's entry authority governed its old value, not
the new one. Shadowing an outer resource binding in an inner block is rejected
by the no-shadowing rule (`83-modules.md` §7), so an inner binding can never
touch an outer authority. Across a control-flow join, a name whose
provenance differs between paths is unknown afterwards, so branches cannot
manufacture disjointness. (Authority roadmap milestone 3, first increment;
projections and aggregate writes remain conservative.) Unknown
provenance and known consumed authority are distinct diagnostic causes. A conflict
involving an unknown argument must identify that argument, including when it is a
shared participant paired with a tracked exclusive participant.

**Callee-entry authority.** A function's own resource contract also governs
its body. Each mode-marked resource parameter enters with exactly the
authority its mode grants: a `borrowed` parameter enters with shared
authority and may be read and forwarded to shared-borrowed positions, but
may neither be passed to a mutable-borrowed position nor consumed; a
`borrowed-mut` parameter may be forwarded to shared and mutable positions but
never consumed; a `consumed` parameter enters with full authority, usable
until its own consumption. An alias of a parameter carries the parameter's
entry authority, so renaming does not launder it. A call that forwards a
parameter beyond its entry authority is rejected with `OAK-B0114`, has not
occurred semantically (it consumes nothing and establishes no fresh
result), and the diagnostic names the parameter declaration and the
offending argument. A borrowed or borrowed-mut parameter is also never
**retained**: returning it (or an alias of it) as the function's result,
directly or through a block or match arm, or storing it in a record or
array literal, is rejected with the same code — the caller keeps custody
of a lent resource, and only consumption transfers it, so a consumed
parameter may be returned. Unmarked parameters keep their ordinary meaning
until a migration rule is chosen. These are the forwarding and retention
increments of the authority roadmap's milestone 1
(`docs/notes/roadmap-authority-resources.md`); escape of storage borrows
(views and spans) remains `OAK-B0109`.

**Contracts across callable boundaries.** A contract belongs to a function's
semantic identity, not to the spelling of a call. A function value
initialized from a global function (`shutdown: (Handle) -> () = close`)
carries that function's contract: calling through the value consumes or
borrows exactly as the direct call would, and invalidates the caller's
aliases the same way. A function value of unknown provenance — a
function-typed parameter, a closure literal, a value that was reassigned —
has an **unknown** contract, and an unknown contract is not an empty one:
passing a resource through such a value is rejected with `OAK-B0115`
rather than treated as harmless. A value initialized from a function with
no contract keeps the ordinary (unmarked) meaning. A contract declared for
a generic template holds for every specialization: the specialized call
sites and the specialized bodies are checked under the template's modes,
so monomorphization cannot lose a mode. **Receiver authority is its own slot.** A method's receiver carries a mode
of its own — `borrowed`, `borrowed-mut`, or `consumed` — declared beside
the explicit parameter modes and never shifting their indices: argument 0
of `fn (h: Handle) merge(other: Handle)` is `other` whether or not the
receiver is marked. At a call `h.merge(g)` the receiver participates in
call-local exclusivity like any argument (a mutable receiver and a borrowed
argument naming one resource is `OAK-B0112`, labeled "receiver"), a
consuming receiver invalidates the caller's handle after the call, and the
method body is checked under the receiver's entry authority (a borrowed
receiver cannot be consumed or retained inside the method). In SemIR the
receiver mode is the `resource.borrow`/`borrow-mut`/`consume` effect with
the parameter `receiver`. A receiver mode is valid only on a method whose
receiver type is a resource type.

**Contracts on function types.** A function-typed parameter may carry a
**callable contract**: the resource modes (and fresh-return fact) required
of any function value passed for it, declared beside the parameter modes of
the enclosing callable. At a call, the function value passed must carry
that contract by **exact normalized agreement** — a consuming function does
not satisfy a borrowed requirement, a function with no contract does not
satisfy a requirement with any mode, and a value of unknown provenance
satisfies none; mismatches are `OAK-B0116`, and the rejected call has not
occurred. Inside the callee, a call through the contracted parameter uses
the declared contract: `op(h)` borrows or consumes exactly as declared, and
forwarding `op` to another contracted position compares the two contracts.
In SemIR the requirement is the `resource.callable-borrow`,
`callable-borrow-mut`, `callable-consume` (`arg:N`, `param:M`) and
`callable-return-fresh` (`arg:N`) effects. Nested callable contracts
(functions of functions) and ownership variance are not admitted until
their substitutability laws are specified.

Imports and sealing cannot erase modes: a protocol declared in one package
(`112-protocols.md` §5, `via close(consumed h)`) is elaborated with the
program's internal names, so the same contract governs every importer's
calls — qualified, open, selective, or through a sealed signature — and the
diagnostics name the qualified spelling.

The callable-boundary audit and proposed result provenance/lifetime relationships
are recorded in [`../resource-contracts-and-results.md`](../resource-contracts-and-results.md).
These proposals do not relax the current borrowed-return restriction.

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

The first step toward this is implemented: an inbound buffer borrow
(`92-ffi.md` §2.7) lets an `unsafe` block view or write runtime-owned memory
for the block's extent under a stated contract. The owning `Buffer` record
that carries a foreign allocation across calls remains the increment after
runtime-sized arenas.

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
- shared resource-call parameters are alias-compatible while mutable-borrowed and consumed parameters require exclusive authority classes;
- rejecting a resource-call alias conflict leaves permanent resource authority unchanged;
- extent propagation preserves the semantic length equations introduced by array views, slices, and proved splits.

`spec/lean/Oak/Borrowing.lean` models the local borrow-state laws. `Oak.ResourceFlow`
models consumption and alias classes, while `Oak.ResourceCall` models call-local
parameter-mode compatibility. Symbolic-extent lemmas should extend that proof
surface as the checker representation lands. Temporal ownership transfer across
asynchronous actors may additionally use TLA+ when introduced.



## Extent facts and proof-based bounds-check elision (implemented subset)

A runtime check the program already performs establishes an **extent fact**
for exactly the scope it dominates, and an element access inside that scope
whose index the fact bounds is emitted without its bounds check. Every
access the checker cannot prove stays checked — elision is the reward for
a check that is already there, never a relaxation.

```oak
sum: (v: []u64): u64 {
  total: u64 = 0
  i: u32 = 0
  while i < len(v) {          // fact for the body: i < len(v)
    total = total + v[i]      // proven: direct element access
    i = i + u32(1)            // the canonical increment, last statement
  }
  total
}

len(a) == len(b) ? {          // fact: len(a) == len(b)
  while i < len(a) { acc = acc + a[i] * b[i] }   // b[i] proven by transfer
}

len(v) >= u32(4) ? v[u32(3)] | u64(0)            // proven: 3 < 4 <= len(v)
regs: [4]u64
regs[u32(1)] = u64(2)                            // proven: static extent
```

Facts (`typechecker/extents.go`, laws in `Oak.Extents`):

- **Min-length**: `len(v) >= K`, `len(v) > K`, `K <= len(v)`, `K < len(v)`
  with `K` a literal (bare or `u32(K)`) proves constant indices below `K`
  (`constant_under_min_length`).
- **Index bound**: `i < len(v)` (or `len(v) > i`) as a `?` condition or a
  `while` condition proves `v[i]`. For the loop, the body must change `i`
  only as its final statement — the canonical increment — so every access
  before it executes under the most recent evaluation of the condition
  (`loop_invariant`).
- **Offset bound**: `i + K < len(v)` (K a literal) proves `v[i + j]` for
  every literal `j <= K` and `v[i]` itself (`offset_under_bound`) — the
  shape of pairwise and multi-byte scans.
- **Same length**: `len(a) == len(b)` transfers an index bound from one
  container to the other (`bound_transfers`).
- **Subslice extent**: `s: []T = subslice(v, start, n)` with a literal `n`
  establishes `len(s) == n`, and `s: []T = v[lo:hi]` with literal bounds
  `len(s) == hi - lo`, for the rest of the enclosing block (the
  construction is bounds-checked — `start + n <= len(v)`, compared without
  overflow — so once it succeeds the extent is exact), unless the block
  later reassigns `s` (`subslice_extent`, `subslice_check_iff`).
  `subslice` lowers to a per-element-type helper that traps past the end
  and otherwise returns `{base + start, n}` — zero copies, one check.
- **Static extent**: a constant index below an owned array's declared
  length needs no fact (`static_extent`).
- Conjunctions (`&&`) contribute every fact of both sides.

Facts are refused, not weakened, whenever soundness would need dataflow
the checker does not perform: a participating binding that is a global (a
callee could reassign it), a scope that reassigns a participating binding
(except the loop's trailing increment), a non-literal bound, or a
condition of any other shape. The true arm of the `?` sugar is the
fall-through under the check; the false arm receives nothing.

In the emitted C a proven access is `( v ).base[ i ]` or `regs[ i ]`; an
unproven one keeps `oak_view_index_*`, `oak_span_index_*`, `oak_index`, or
`oak_store` — asserted by tests on both sides, with an out-of-range
unproven access still trapping. This is roadmap milestone 8's first
increment (`docs/notes/roadmap-authority-resources.md`) and the seed of
milestone 9's bounds-check elimination; the assembler's span guards
(`94-assembler.md` §7) are the same doctrine in hand-written code.
