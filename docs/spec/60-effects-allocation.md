# Effects and Allocation

Oak makes material runtime behavior explicit in the semantic model.

## 1. Effects

An effect names an operation class that is observable for correctness, authority, scheduling, or cost analysis.

Conceptually:

```text
Memory.Allocate[allocator]
Thread.Block
Os.Syscall
Mmio[device]
Io[channel]
```

Effects may be parameterized by a semantic identity such as an allocator, device, channel, or authority.

An unparameterized effect denotes the whole class:

```text
Memory.Allocate
```

therefore overlaps every `Memory.Allocate[x]`.

## 2. Effects and forbids (implemented subset)

A function may declare the effects it performs and may forbid classes of
effect. The v1 surface is two clauses after the signature, in either order,
each at most once:

```oak
grow: (n: u32): u32 effects { Memory.Allocate } = ...
process: (frame: []u8): u32 forbids { Memory.Allocate, Thread.Block, Os.Syscall } = ...
c_abs: (n: c.Int32): c.Int32 effects { } = c.extern("abs")
```

An effect is a `Namespace.Name` class (`semir.Effect`); parameterized
instances (`Memory.Allocate[arena]`) are direction and, per the semantic IR,
an unparameterized name overlaps all of its instances.

Rules, checked after specialization over the concrete call graph
(compiler/effects.go):

- The effects reachable from a function are its own `effects` clause and,
  transitively, those of every function it calls by name. Builtins and width
  conversions carry none.
- `forbids { E }` rejects the program when `E` is reachable (`OAK-E0101`,
  naming the call path that carries it), and when the function itself
  declares `E` (`OAK-E0102`, the static contradiction).
- Facts are never guessed. An extern (`c.extern`) or asm-backed declaration
  without an `effects` clause has unknown effects, and so does a call
  through a function value (a parameter or local of function type); a
  `forbids` that reaches either is rejected (`OAK-E0103`). `effects { }` on
  an extern asserts it performs none, on the author's authority.
- Clauses have no runtime representation and no effect on layout or ABI.

Ordinary Oak allocates nothing (section 3), so today `Memory.Allocate` and
the other classes enter a program only through declared externs and
declared Oak functions; the clauses make those entry points explicit and let
a hot path prove, transitively, that it reaches none of them. Effect
inference for undeclared Oak functions is exactly this closure; a function
need not declare what its callees declare.

### 2a. Effect rows on function types

A function type may carry an effect row:

```oak
launch: (step: ([]u8) -> () effects { }, buf: []u8): () forbids { Host.Read } = step(buf)
```

`(T) -> R effects { A.B, ... }` is a type; a value of that type performs at
most the effects in the row. The row is written after the return type,
binds to the innermost function type, and appears at most once; a function
statement that returns a function type and declares its own clause
parenthesizes the return type. Rows do not take part in type identity —
`(u32) -> u32` and `(u32) -> u32 effects { }` are the same type to the
checker — and have no runtime representation; they are facts for the effect
analysis:

- **A call through a rowed value is known.** It contributes exactly the
  row's effects to the caller's closure, so a `forbids` that reaches it
  passes when the row excludes the effect and is rejected with the value's
  name when the row carries it (`OAK-E0101`: "which it may perform through
  the function value step"). A call through a value without a row stays
  unknown (`OAK-E0103`) as before.
- **A value entering a rowed type is checked against the row**
  (`OAK-E0105`), at the two positions where a value enters: an argument for
  a parameter of the type, and the initializer of a declaration with the
  type. The value's reachable effects — declared clauses, rows of the values
  it calls, transitively through its callees after specialization — must
  all lie in the row, and must be known: a value that reaches an undeclared
  extern, a call through an unrowed value, or an expression the analysis
  cannot follow is rejected. A function named in the program, a rowed
  parameter or local (its row must be inside the target row — a narrower row
  fits a wider one), and a function literal (analyzed like a body) are the
  admitted forms. Other flows — assignment after declaration, record fields,
  return values — are not checked and so a rowed value obtained through
  them is trusted only where its declaration was checked.
- Rows are checked whenever the program contains one, with or without a
  `forbids`; the diagnostic names the function, the slot, the row, the
  offending effect, and the call path that reaches it.

This is the pilot's "effect-typed step": a step declared as `([]u8) -> ()
effects { }` may be launched from a function that forbids host reads, and a
step body that reads the host — by calling `Host.Read`-declared externs —
is a compile error at the launch, naming the reader. `Oak.EffectRows`
(`spec/lean/Oak/EffectRows.lean`) models the check: `bound` is the compiler's
static closure over own effects, slot rows, and callees; `perform` is what a
run with concrete functions installed in the slots may do;
`perform_subset_bound` proves that under the row check every performed
effect is in the bound, and `forbids_sound` that a `forbids` on a function
whose bound excludes the effect holds for every admitted run.

## 3. No hidden allocation

Ordinary language constructs do not allocate unless their semantics explicitly carry an allocation effect.

This includes:

- generic dispatch;
- pattern matching;
- conversions;
- interface constraints;
- iterator/combinator use;
- closure capture;
- string conversion;
- collection construction beyond fixed/caller-provided storage;
- explicit parallel combinators whose selected implementation does not declare allocation.

If an implementation strategy would require allocation, either another allocation-free lowering must be used or the operation must expose/require an allocator effect.

## 4. Effect ordering and transformations

The presence or absence of effects is a semantic input to optimization legality.

A compiler transformation may reorder, duplicate, fuse, eliminate, or execute operations concurrently only when doing so preserves every observable effect contract involved.

Effects such as the following are normally order-sensitive unless their specific contract states otherwise:

```text
Io[channel]
Mmio[device]
Thread.Block
Os.Syscall
volatile/atomic/synchronization operations when modeled as effects or equivalent machine obligations
```

Two operations having the same broad effect class does not by itself make them interchangeable or reorderable. Parameter identities and operation semantics matter.

Pure/empty-effect computation provides the widest rewrite freedom, subject still to machine numeric semantics, borrowing/resource flow, traps, and representation obligations.

Explicit parallel constructs do not weaken this rule. A parallel callback must satisfy the operation's required/forbidden effect contract, and an implementation must not introduce scheduler allocation, blocking, or syscalls that the source/profile forbids. See `55-parallelism`.

## 5. Allocation strategies are ordinary types

Oak should not need special grammar for common allocation policies.

Examples:

```oak
Arena[R]
Slab[T, N]
Pool[T, N]
Handle[T]
```

These are ordinary semantic/library types whose parameters carry facts that the checker/proof system can use.

## 6. Arenas / regions

An arena groups many allocations under one lifetime identity `R`.

```text
Arena[R]
```

Properties:

- allocation is cheap and monotonic or otherwise region-governed;
- individual objects normally do not have independent deallocation;
- all region-bound values must die before or with `R`;
- resetting/freeing the arena invalidates values tied to the region.

An arena operation has an allocation effect scoped to that arena identity.

The type/proof system should be able to express that `T[R]` cannot safely escape `R`.

Implemented subset: `Buffer[T]` (`92-ffi.md` §2.8) is the runtime-sized
owner — memory a runtime allocated, held by one binding from `c.own` to
`c.disown` — and the `arena` package reserves aligned element ranges over
it, handing out offsets the program carves with `subslice` over the
buffer's views and spans. The region identity `R` is the buffer's owner
identity in the borrow checker: nothing derived from the buffer outlives
its block, and the buffer cannot be borrowed after `c.disown`.

## 7. Slabs / pools

A bounded typed slab:

```oak
Slab[T, N]
```

owns storage for at most `N` live `T` slots.

Static capacity is a semantic fact and can support proofs of:

- occupancy never exceeds `N`;
- allocation failure is explicit when full;
- no allocation outside pre-owned backing storage;
- slot reuse obeys generation rules when handles are used.

No general heap behavior is implied.

## 8. Handles

`Handle[T]` is object identity, not a pointer synonym and not an allocator.

A common representation is:

```text
slot + generation
```

with the safety law:

```text
generation mismatch -> lookup fails
```

After a slot is freed/reused, stale handles must not resolve to the new object.

Pointer values may locate bytes; handles identify logical objects.

## 9. Caller-provided storage

For many systems APIs, caller-owned storage should be the ergonomic default:

```oak
fn encode(dst: [*]u8, value: T): Result[[]u8, Error]
```

rather than a result type that implies hidden allocation.

This makes ownership, capacity, and failure behavior visible.

## 10. Stack/static storage

Stack and static storage are also explicit lifetime/storage strategies even when they require no allocator object.

The compiler may choose stack placement for non-escaping values as an optimization/refinement of explicit value semantics. It must not silently move an escaping value to the heap.

### 10a. Static storage initializers

A top-level binding is static storage, initialized before any code runs.
Its initializer is a compile-time constant or absent (zero initialization):

- literals, arithmetic over literals, and primitive casts of constants,
  which the C backend emits as C constant expressions;
- the named conversions of `20-types.md` §11.1 and §11.3.4 other than
  `checked`, and the float constructors `f32(x)`/`f64(x)`, applied to
  constants — a rounded threshold `HALF: f16 = f16_round_f32(0.5)`, a
  quantization table `[4]bf16{ bf16_round_f32(1.0), ... }`, a reinterpreted
  bit pattern — which the backend **folds**: the initializer is evaluated
  by the interpreter, the first witness of every conversion's bit-exact
  semantics, and emitted as the literal of the initializer's type (hex
  float, storage bits, or integer). The differential tests hold the
  interpreter to the C helpers, so the folded constant is the value the
  program would compute at run time;
- a read of a constant global declared **earlier** in the file, folded
  with it (`CELLS: u32 = ROWS * COLS`);
- record and array literals of the above.

Anything else — a call to an ordinary function, a read of a later or
non-constant global, an intrinsic — is not constant. `OAK-T0501` warns at check time (script
programs may still interpret such a binding, initializing it at load), the
strict profile rejects it, and **C emission fails with `OAK-T0501` as an
error** naming the global and its position. The generated C never runs a
hidden global constructor, and the failure is Oak's diagnostic, never the
C compiler's (ml finding F19). Runtime initialization is written at the top
of `main`.

## 11. Closures

A capturing closure has an environment whose storage must be justified by ownership analysis.

Non-escaping captures can use stack/static/caller-owned storage.

If capture escape requires arena/slab/heap allocation, the effect is explicit and subject to `forbids` checks.

Enforcement today: captureless function literals are accepted as bare code pointers; capturing closures are rejected (`OAK-T0401`) until a storage justification surface exists, per `Oak.ClosureCapture`.

Static higher-order specialization may eliminate a callable wrapper or closure representation only when the specialized lowering preserves the same ownership and effect semantics. It must not use specialization as a way to hide an otherwise-required allocation.

## 12. Realtime/bounded code

A realtime/bounded function should be able to establish structural properties such as:

```text
no allocation
no blocking
no syscall
bounded loops / bounded recursion policy
bounded queue operations
```

These are stronger than merely “lock-free.”

The effect system is one source of evidence; boundedness/resource proofs are additional propositions.

Explicit parallelism is realtime-safe only when its execution resources, scheduling, synchronization, and boundedness satisfy the same profile. A general-purpose task runtime is not implicitly permitted merely because the source uses a parallel combinator.

## 13. Formal verification targets

Initial Lean proof targets:

- effect overlap is symmetric;
- unparameterized effect class overlaps all parameterized instances of the same class;
- distinct parameterized instances do not overlap unless parameters are equal;
- required/forbidden overlap is rejected;
- effect-aware transformations preserve modeled observable order;
- explicitly parallel lowering does not introduce effects forbidden by the source/profile contract;
- slab occupancy cannot exceed static capacity under valid transitions;
- stale generation cannot resolve after slot reuse;
- region-bound values cannot outlive their region in the abstract lifetime model.

`spec/lean/Oak/Effects.lean` proves the effect-overlap laws, `spec/lean/Oak/Slab.lean` the capacity law, and `spec/lean/Oak/Handles.lean` the stale-generation and cleared-slot laws. The semantic IR's `semir.HandleTable` implements the handle operations as transliterations of `Oak.Handles` (`Resolve` = `Resolves`, `Free` = `clear`, reuse advances the generation before re-occupancy); the concrete 32-bit generation space fails closed by retiring an exhausted slot rather than wrapping it.
