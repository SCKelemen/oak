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

In particular, ordinary IEEE floating-point addition must not be silently treated as mathematically associative under default strict machine semantics. `20-types.md` §11.3 fixes those semantics (no reassociation, no contraction, in any backend) and takes the fourth option for the one reduction it defines: `simd.reduce_add` over a float vector is a specified pairwise tree.

The standard library's `reduce` package (`import("reduce")`) is the fourth
option for views of any element type: `reduce.tree(xs, zero, f)` combines a
view in the **balanced binary-counter tree** — a stack of partial results
with levels; each element enters at level 0 and combines with its neighbour
whenever the two newest partials share a level, earlier operand on the left;
the leftovers combine right to left — so four elements give
`f(f(x0, x1), f(x2, x3))`, exactly `simd.reduce_add`, and any count gives one
fixed tree that C, the interpreter, and `Oak.Reduce` (Lean) compute
identically (`tree_four`, `tree_eight`). `reduce.left(xs, zero, f)` is the
sequential left fold. The first option is `laws { associative }` on an
operator definition (`10-syntax.md` §14a): `Oak.Reduce.tree_assoc` proves
that under associativity the tree equals the left fold from the first
element, which is what licenses a backend to choose any grouping for such
an operation, and the type checker uses it: `reduce.tree` over an operator
declaring the law is lowered to `reduce.chain`, that left fold
(`tree_eq_chainFold`). Without the law it computes the tree named.

**An order is a function.** When a program needs a second order beside
the one it computes with — the fused attention's online-softmax merge,
carrying `(max, sum)` across a window, beside the lane rule — the order
is written as an Oak function and named as one: `reduce.fold(xs, init,
step)` is the sequential order with a state of its own type, and
`reduce.tree_map(xs, zero, lift, merge)` the binary-counter order over
the lifted elements. Each function's extraction is its declaration, and
a theorem relates the two: `Oak.Reduce.fold_eq_tree_map` proves that for
an associative merge `fold(xs, lift(x0), step)` with `step(s, x) =
merge(s, lift(x))` equals `tree_map(xs, zero, lift, merge)` on non-empty
input, as `tree_assoc` relates `tree` to `left` and `coop_eq_tree` the
cooperative scheme to `tree`. Reorder permission is therefore not a
separate annotation: it is `laws { associative }` on the merge, and the
theorem that names which two orders it makes equal. The canonical order
is the one the program calls; the grouping named is the grouping
computed.

**Declaring the order once.** A block may declare the order for every
reduction inside it, so a routine says it once rather than at each call:

```oak
order left {                       // every reduce.reduce here is the left fold
  s: f32 = r.reduce(view(&xs), zero, plus)
}
order any {                        // permission to regroup — needs the claim
  t: Sum = r.reduce(view(&sums), Sum { v: 0 }, add)   // add declares associative
}
```

`reduce.reduce(xs, zero, f)` is the reduction whose order the enclosing
`order` block names: `tree` (the binary-counter tree), `left` (the
sequential fold), or `any` — the permission to regroup, which lowers the
call to `reduce.chain` and is **refused** unless `f` is an operator
declaring `laws { associative }` (`10-syntax.md` §14a): without the claim
the checker reports the call and names the two spellings that state the
intent. Outside every order block `reduce.reduce` is `tree`: **the exact
order is the default**, and nothing regroups unless a block says `any`
and the operator carries the claim. The innermost block wins; an explicit
`reduce.tree` or `reduce.left` keeps its name inside any block. The
checker rewrites each call to the order it resolved to, so the C backend,
the interpreter, and the extraction see a named order (the semantic model
lists the rewrites, `LawLowerings`), and the theorems above relate the
orders — `tree_eq_chainFold` is what `any` rests on. The precise reading
for floating point: under `order any`, a reduction over an `f32` add
declared associative computes *some* grouping's value — a **bounded**
quantity — while `order tree`, `order left`, and the default compute the
exact named grouping bit for bit. The bound is a theorem
(`Oak.FloatBounds`, over the rounding model of `Oak.Floats`: a value is an
integer rounded to `p` significant bits after every addition, `u = 2^-p`
the unit roundoff):

- `round_error`: one rounding moves a value by at most `u·|x|`
  (`2^p · |round p x − x| ≤ |x|`).
- `rounded_error`: for **any grouping** of the additions, of depth `d`
  over leaves `xᵢ`, the computed sum is within `((1 + u)^d − 1) · Σ|xᵢ|`
  of the exact sum — stated over the integers as
  `2^(p·d) · |rounded − exact| ≤ B p d · Σ|xᵢ|` with
  `B p d + 2^(p·d) = (2^p + 1)^d` (`bound_closed`), so the reading needs
  no first-order approximation.
- `chain_error`: `reduce.chain` — the left fold from the first element,
  what `any` lowers the reduction to — is the grouping of depth `n − 1`
  over `n` values, so what Oak computes under `order any` is within
  `((1 + u)^(n−1) − 1) · Σ|xᵢ|` of the exact sum.
- `groupings_differ`: two groupings of the same values differ by at most
  the sum of their bounds — the distance between any two orders a
  program might name, and the whole content of "bounded".

- `tree_is_grouping`: `reduce.tree` over a non-empty list is the rounded
  sum of some grouping of exactly those leaves, so `rounded_error` bounds
  it by that grouping's depth and `groupings_differ` bounds its distance
  from the chain.
- `tree_depth_log`, `tree_error_log`: that grouping's depth is at most
  `bitlen n` — `⌊log₂ n⌋ + 1` — so `reduce.tree` over `n` values is within
  `((1 + u)^(⌊log₂ n⌋ + 1) − 1) · Σ|xᵢ|` of the exact sum, against the
  chain's `((1 + u)^(n−1) − 1) · Σ|xᵢ|`. The proof follows the binary
  counter: a partial at level `k` is a grouping of depth at most `k` over
  exactly `2^k` leaves (`Levels`), the levels ascend from the head down
  (`Ascending`), so every level is below `bitlen n`, and the leftover
  merges (`finish`) end at most one deeper than the bottom's level.

The claim `laws { associative }` on a floating-point add is therefore a
permission with a stated cost, not a lie about the format. The bound is
over the idealized format without overflow or subnormals, as `Oak.Floats`
is. `commutative` is recorded with `associative` and
consumed by nothing yet; a backend that reorders operands, not just
groupings, is what would read it.

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
