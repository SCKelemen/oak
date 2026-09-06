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

## 2. Requires and forbids

A function may require effects/authority and may forbid classes of effect.

Conceptually:

```oak
fn build[R](arena: Arena[R]): Graph[R]
  effects { Memory.Allocate[arena] }
```

Realtime code can prohibit broad classes:

```oak
realtime fn process(...)
  forbids { Memory.Allocate, Thread.Block, Os.Syscall }
```

Exact surface syntax is not yet frozen. The semantic rule is normative.

A required effect and a forbidden overlapping effect is a static contradiction.

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
- collection construction beyond fixed/caller-provided storage.

If an implementation strategy would require allocation, either another allocation-free lowering must be used or the operation must expose/require an allocator effect.

## 4. Allocation strategies are ordinary types

Oak should not need special grammar for common allocation policies.

Examples:

```oak
Arena[R]
Slab[T, N]
Pool[T, N]
Handle[T]
```

These are ordinary semantic/library types whose parameters carry facts that the checker/proof system can use.

## 5. Arenas / regions

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

## 6. Slabs / pools

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

## 7. Handles

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

## 8. Caller-provided storage

For many systems APIs, caller-owned storage should be the ergonomic default:

```oak
fn encode(dst: [*]u8, value: T): Result[[]u8, Error]
```

rather than a result type that implies hidden allocation.

This makes ownership, capacity, and failure behavior visible.

## 9. Stack/static storage

Stack and static storage are also explicit lifetime/storage strategies even when they require no allocator object.

The compiler may choose stack placement for non-escaping values as an optimization/refinement of explicit value semantics. It must not silently move an escaping value to the heap.

## 10. Closures

A capturing closure has an environment whose storage must be justified by ownership analysis.

Non-escaping captures can use stack/static/caller-owned storage.

If capture escape requires arena/slab/heap allocation, the effect is explicit and subject to `forbids` checks.

## 11. Realtime/bounded code

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

## 12. Formal verification targets

Initial Lean proof targets:

- effect overlap is symmetric;
- unparameterized effect class overlaps all parameterized instances of the same class;
- distinct parameterized instances do not overlap unless parameters are equal;
- required/forbidden overlap is rejected;
- slab occupancy cannot exceed static capacity under valid transitions;
- stale generation cannot resolve after slot reuse;
- region-bound values cannot outlive their region in the abstract lifetime model.

`spec/lean/Oak/Effects.lean` begins with the effect-overlap laws. Slab/handle proofs should be added once their implementation representation is stabilized.
