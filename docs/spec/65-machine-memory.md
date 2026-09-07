# Machine memory: atomics, volatile access, and ordering

This chapter specifies Oak's executable machine-memory contract: fixed-width
integer atomic cells, explicit memory order, strong compare-exchange,
allocation-free source operations, and raw volatile access. Device MMIO,
architecture barriers, system registers, and inline assembly build on this
layer but remain separate contracts.

> Memory effects that matter to hardware or concurrency are language semantics,
> never backend accidents.

## 1. Atomic cells

`Atomic[T]` is storage identity for one atomically accessed machine cell.
Atomicity belongs to the cell and its accesses; a value loaded or returned by
an RMW/CAS from `Atomic[u32]` is an ordinary `u32`.

The v1 carriers are exactly `u8/u16/u32/u64` and `i8/i16/i32/i64`.
Native-width integers, pointers, booleans, records, sums, and aggregates are not
v1 carriers. Their width, provenance, layout, or lock-freedom contracts must be
specified before they can become atomic carriers.

A source cell is declared directly:

```text
counter: Atomic[u64]
```

It is zero-initialized and has storage identity. Direct assignment/copy,
ordinary arithmetic/matching, by-value argument/return transport, aggregate
embedding, and temporary-cell operands are rejected. A future borrowed
`AtomicRef[T]` may transport cell identity without copying it; v1 does not
manufacture an implicit pointer or heap wrapper.

## 2. Single-operation memory orders

Oak defines `relaxed`, `acquire`, `release`, `acq-rel`, and `seq-cst`.
Orders are semantic compile-time facts and backends may not guess or silently
change them.

| Operation | relaxed | acquire | release | acq-rel | seq-cst |
| --- | --- | --- | --- | --- | --- |
| load | yes | yes | no | no | yes |
| store | yes | no | yes | no | yes |
| read-modify-write | yes | yes | yes | yes | yes |
| fence | no | yes | yes | yes | yes |

Illegal combinations such as release-load, acquire-store, and relaxed-fence
have no source builtin.

## 3. Strong compare-exchange

Compare-exchange has two orders because success performs an RMW while failure
performs only a read. The legal `(success, failure)` pairs are exactly:

| success | legal failure orders |
| --- | --- |
| relaxed | relaxed |
| acquire | relaxed, acquire |
| release | relaxed |
| acq-rel | relaxed, acquire |
| seq-cst | relaxed, acquire, seq-cst |

Failure can never be `release` or `acq-rel`, and it can never be stronger than
success.

Oak exposes **strong** CAS only in this slice: no spurious failure. Its API is
value-oriented rather than C's mutable `expected*` convention:

```text
observed = atomic_compare_exchange_<success>_<failure>(cell, expected, desired)
```

The operation atomically compares the cell with `expected`. If equal, it writes
`desired` and returns `expected`. If unequal, it does not write and returns the
value observed by the failed comparison. Therefore:

```text
observed == expected    => success
observed != expected    => failure; observed is the retry value
```

For fixed-width integer carriers this preserves all information needed by a
CAS loop without adding an out-parameter, reference wrapper, allocation, or
second mandatory load.

The exact source constructors are:

```text
atomic_compare_exchange_relaxed_relaxed
atomic_compare_exchange_acquire_relaxed
atomic_compare_exchange_acquire_acquire
atomic_compare_exchange_release_relaxed
atomic_compare_exchange_acq_rel_relaxed
atomic_compare_exchange_acq_rel_acquire
atomic_compare_exchange_seq_cst_relaxed
atomic_compare_exchange_seq_cst_acquire
atomic_compare_exchange_seq_cst_seq_cst
```

Each takes `(cell, expected, desired)` and returns carrier `T`. No other order
pair has a source constructor.

## 4. Other normative atomic operations

Loads:

```text
atomic_load_relaxed(cell) -> T
atomic_load_acquire(cell) -> T
atomic_load_seq_cst(cell) -> T
```

Stores:

```text
atomic_store_relaxed(cell, value) -> ()
atomic_store_release(cell, value) -> ()
atomic_store_seq_cst(cell, value) -> ()
```

Fetch-add returns the pre-add value and exists for all five orders. Fences exist
for acquire, release, acq-rel, and seq-cst. Atomic exchange remains a backend
building block but is not yet a normative source builtin.

## 5. Effects and shared semantic authority

Atomic operations project into the effect axis as:

```text
Memory.AtomicLoad[order]
Memory.AtomicStore[order]
Memory.AtomicRMW[order]
Memory.AtomicCompareExchange[success_order, failure_order]
Memory.AtomicFence[order]
```

One Semantic-IR builtin descriptor owns source identity, operation kind, arity,
order(s), result shape, legality, effect projection, checker behavior, evaluator
behavior, and backend selection. CAS legality is therefore not independently
reimplemented as unrelated source and backend tables.

Atomic operations do not semantically imply allocation, blocking, scheduler
interaction, I/O, or syscalls.

## 6. Allocation and performance contract

The machine-memory performance contract is structural:

1. `Atomic[T]` lowers to inline `_Atomic(T)` storage;
2. atomic operations allocate no Oak heap object;
3. all memory orders are compile-time data; there is no runtime order enum;
4. load/store/fetch-add/fence lower directly to explicit C11 primitives;
5. strong CAS lowers to `atomic_compare_exchange_strong_explicit` through
   `static inline` helpers and C11 `_Generic` carrier selection;
6. CAS helpers carry success/failure orders as constants, never runtime
   `memory_order` arguments;
7. semantic builtin lookup is regression-tested at zero Go allocations;
8. `<stdatomic.h>` and CAS helper source are pay-for-use;
9. generated hot paths are checked for accidental heap calls or order switches.

This removes Oak runtime overhead around the primitive. It does not claim every
backend/target implements every carrier lock-free. Freestanding and hard-RT
target profiles must establish required atomic operations are lock-free (or
otherwise have an accepted bounded implementation) before admission.

CAS retry count is not intrinsically bounded under contention. Realtime code
must account for that explicitly; lock-free does not mean hard-realtime.

## 7. C11 bootstrap refinement

The bootstrap backend uses `_Atomic(T)`, `atomic_*_explicit`, and exact
`memory_order_*` constants. Strong CAS uses a local C `observed` value initialized
to Oak's expected value, invokes `atomic_compare_exchange_strong_explicit`, and
returns the resulting `observed`. C's expected-value update semantics therefore
refine directly to Oak's value-returning CAS contract.

C11 `_Generic` selects the fixed-width carrier helper at compile time. There is
no Oak runtime type/order dispatch and no heap allocation.

This is an executable backend refinement, not yet a formal proof that every C
compiler and ISA implementation satisfies Oak's complete memory model.

## 8. Reference evaluator

The Go evaluator keeps one persistent `sync/atomic.Int64` cell per Oak atomic
cell. It executes load/store/fetch-add and sequential strong-CAS value semantics.
Go atomics over-strengthen several Oak order variants, so the evaluator is not
a weak-memory oracle. Exact order behavior belongs to generated-C/ISA tests and
the formal memory model.

## 9. Volatile access

Volatile means the requested observable machine access must not be removed,
duplicated, or replaced by an ordinary cached language value. Its effects are
`Memory.VolatileRead` and `Memory.VolatileWrite`.

Volatile is not atomic synchronization and is not by itself a complete MMIO
ordering contract. AArch64 device-memory type, access width, DMB/DSB/ISB, DMA
coherency, and interrupt-entry ordering belong to later machine chapters. Raw
volatile C lowering intentionally adds no hidden fence.

## 10. Formal verification

`spec/lean/Oak/MemoryOrder.lean` kernel-checks both the single-order matrix and
strong-CAS relation. It proves, among other facts:

- illegal load/store/fence orders are absent;
- every ordinary source builtin satisfies the applicable legality rule;
- CAS failure can never be release or acq-rel;
- relaxed-success CAS permits only relaxed failure;
- release-success CAS permits only relaxed failure;
- the exact nine CAS source constructors all satisfy `casLegal`;
- every source CAS constructor has a legal success/failure pair;
- no source CAS can expose release/acq-rel failure ordering.

These are language-level proofs. C/ISA refinement and the complete
happens-before model remain separate proof obligations.

## 11. End-to-end tests

Acceptance spans the whole executable stack:

- parser/typechecker validate the exact CAS spellings, cell identity, arity, and
  carrier-typed expected/desired values;
- Semantic IR tests enumerate legal/illegal CAS pairs and keep lookup
  zero-allocation;
- evaluator tests execute both success and mismatch paths, including returned
  observed values and unchanged-on-failure storage;
- generated C is checked for strong C11 CAS, exact order constants, no heap
  calls, and no runtime order dispatch;
- native C execution validates CAS success/failure semantics;
- four pthreads perform 25,000 CAS-loop increments each against the same
  Oak-generated atomic cell; the exact final value is checked;
- the contention harness records total attempts and retries so CAS retry cost is
  explicit and measurable rather than hidden;
- ordinary Go CI, race-enabled integration where configured, golden output, and
  Lean proofs gate merge.

## 12. Verification status

| Layer | Status |
| --- | --- |
| atomic storage/source semantics | specified |
| single-order legality | proved in Lean |
| strong-CAS success/failure legality | proved in Lean |
| exact CAS source constructors | proved in Lean |
| parser/typechecker/evaluator | implemented + tested |
| C11 strong-CAS lowering | implemented + native-tested |
| compiler semantic lookup allocation | tested at zero allocations |
| contended CAS linearized final value | native-tested |
| CAS retry instrumentation | native-tested |
| C/ISA formal refinement | not yet proved |
| complete happens-before/data-race model | not yet specified |
| AArch64 weak-memory litmus suite | not yet implemented |
| target-specific lock-free admission | not yet implemented |

Next machine-memory work should define Oak's complete happens-before/data-race
model and then verify the AArch64 refinement with weak-memory litmus tests. Only
then should higher-level SPSC/MPSC queue proofs rely on these atomics as their
shared memory foundation.
