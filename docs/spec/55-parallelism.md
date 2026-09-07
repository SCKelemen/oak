# Explicit Data Parallelism

Oak may support data parallelism without making ordinary control flow implicitly concurrent. Parallel execution is a semantic choice that must remain visible in source, auditable in lowering, and compatible with Oak's ownership, effect, proposition, and machine-semantics rules.

## 1. Explicit parallel constructs

Ordinary loops and ordinary functional combinators are sequential unless their API explicitly promises otherwise.

Oak's data-parallel surface should be a small algebra of operations whose semantics grant the implementation scheduling freedom. Conceptually:

```oak
par.map
par.for
par.reduce
par.scan
```

Exact names and syntax are not frozen. The normative property is explicitness: the compiler must not silently turn an ordinary loop into concurrent execution merely because dependence analysis suggests it could.

This preserves two useful facts at once:

- sequential source retains predictable ordering semantics;
- parallel source gives the compiler enough semantic information to choose threads, vector lanes, GPU workgroups, or another target-appropriate implementation when the target and effects permit it.

## 2. Parallel iteration independence

A parallel iteration space is legal only when simultaneously executed iterations cannot violate Oak's semantic rules.

For read-only inputs, multiple iterations may share read authority.

For writable outputs, the compiler must establish that concurrently writable regions are pairwise disjoint or are mediated by an operation with explicit synchronization/reduction semantics.

Conceptually, for an indexed output span:

```text
write_region(i) ∩ write_region(j) = ∅  for all i != j
```

A common `par.map(input, output, f)` can therefore be accepted when the checker establishes facts such as:

```text
Extent(input) = Extent(output)
write_region(i) = output[i .. i+1)
pairwise_disjoint(write_region)
```

The proof may arise from symbolic extents, range analysis, library contracts, or other propositions. Unknown independence fails closed for safe parallel mutation.

## 3. Effects inside parallel operations

Parallel execution does not erase ordinary effect semantics.

A parallel callback or loop body must satisfy the effect contract of the parallel operation. An implementation or profile may, for example, forbid:

```text
Thread.Block
Os.Syscall
Memory.Allocate
```

or may require stronger restrictions for a GPU/realtime lowering.

Observable effects whose relative order matters cannot be freely reordered across iterations. This includes I/O, MMIO, volatile access, conflicting mutation, synchronization, traps whose ordering is observable under the selected machine semantics, and any future effect class whose contract is order-sensitive.

If an operation explicitly provides ordering or synchronization semantics, those semantics are part of its cost and effect contract rather than an implementation accident.

## 4. Reduction semantics

A parallel reduction combines many values using a binary operation. Parallel tree reduction generally changes grouping relative to a left-to-right sequential fold.

Oak must not assume mathematical associativity when machine semantics do not justify it.

A `par.reduce`-like operation therefore requires a contract that makes regrouping legal. That contract may come from one of:

- an operator/type law that is statically known to be associative for the relevant values;
- an explicit algebra object or trait whose contract states the required laws;
- a programmer-selected numeric mode that permits reassociation;
- a specified deterministic reduction tree whose grouping is itself the operation's semantics.

In particular, ordinary IEEE floating-point addition must not be silently treated as mathematically associative under default strict machine semantics.

The identity element, if required by the operation, is likewise a semantic law and not merely an optimization hint.

## 5. Work and span

Parallel APIs should document two algorithmic cost dimensions in addition to Oak's ordinary allocation/effect costs:

- **work** — total amount of computation performed;
- **span** — length of the longest dependency chain, assuming sufficient parallel resources.

For example, a balanced reduction over `N` elements may have `O(N)` work and `O(log N)` span, while a strictly sequential left fold has `O(N)` work and `O(N)` span.

These are semantic cost contracts at the algorithm/library level, not promises of wall-clock speed. Actual execution also depends on target resources, scheduling overhead, memory hierarchy, vector width, and implementation strategy.

Compiler tooling should be able to expose whether an explicitly parallel operation lowered sequentially, vectorized, multi-threaded, or to another backend strategy on a given target.

## 6. Fusion and transformation legality

Oak may fuse adjacent combinators, inline callbacks, vectorize loops, tile iteration spaces, or reorder independent computations when the transformation preserves all observable semantics.

Legality is derived from semantic facts, not from the surface name of an optimization.

A transformation must preserve, as applicable:

- value results and machine numeric semantics;
- borrow/provenance laws;
- consumption and resource flow;
- effect ordering and authority;
- traps/panics whose relative observability is specified;
- allocation identity/lifetime when observable;
- synchronization semantics;
- volatile/MMIO semantics;
- representation and ABI obligations.

Pure/empty-effect code with proved independence gives the optimizer the largest equational rewrite space. Effectful code narrows that space according to the effects' contracts.

An implementation must not justify a semantic change by calling it fusion, vectorization, reassociation, or parallelization.

## 7. Higher-order specialization

Higher-order ergonomic code should not imply runtime indirect dispatch when the callable is statically known.

For a statically known callback, compilation should be capable of:

1. generic specialization/monomorphization;
2. static callable specialization or defunctionalization;
3. elimination of statically known closure/callable wrappers;
4. combinator lowering to ordinary semantic control flow;
5. borrow, proposition, and effect checking on the specialized program;
6. target lowering.

A captureless lambda supplied directly to a combinator should therefore be able to become a direct loop body rather than an indirect function-pointer call. Capturing closures remain subject to the storage and escape rules in `05-ergonomics-and-cost` and `60-effects-allocation`.

First-class runtime callables remain possible when explicitly represented; they simply do not become the hidden implementation strategy for static higher-order code.

## 8. Parallelism and realtime code

Explicit parallelism is not automatically realtime-safe.

A realtime profile must account for scheduling, synchronization, queueing, target resource availability, and boundedness. A parallel operation that can block on a general-purpose scheduler or allocate task objects violates a realtime contract that forbids those effects.

Realtime-safe parallel primitives may exist when their execution resources and bounds are explicit, for example fixed worker sets, static partitions, bounded queues, or target-specific SIMD execution.

The source operation's effect/cost contract must distinguish these cases.

## 9. Diagnostics

When safe parallelization is rejected, diagnostics should identify the missing semantic fact rather than report a generic "cannot parallelize" error.

Useful explanations include:

```text
cannot prove writes for iterations i and j are disjoint
callback may perform Thread.Block, which this parallel operation forbids
reduction operator is not known to permit reassociation
input and output extents are not proven equal
resource consumed in one iteration may be used by another iteration
```

If a symbolic extent or region proof fails, the diagnostic should trace the programmer-visible origins of the conflicting symbols/ranges.

## 10. Formal verification targets

The parallel semantic model should establish at least:

- pairwise-disjoint mutable iteration regions admit no concurrent write/write alias conflict;
- parallel read sharing preserves ordinary shared-read laws;
- reduction regrouping is admitted only under the selected algebra/numeric contract;
- transformation legality preserves the modeled observable effect order;
- explicit parallel lowering does not introduce an effect forbidden by the source/profile contract;
- work/span annotations describe the library algorithm independently of backend scheduling policy.

The local independence and extent/range obligations are suitable Lean targets. Temporal scheduler, queue, and actor properties may additionally use TLA+ where concurrency history is the relevant proof object.
