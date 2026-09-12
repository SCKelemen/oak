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
ordinary arithmetic/matching, by-value argument/return transport, and
temporary-cell operands are rejected.

Cells also embed as **storage**: a record field may be `Atomic[T]` or an
owned array of cells (`[N]Atomic[T]`), and atomic arrays may be declared
directly. A record or array containing cells is itself storage identity —
zero-initialized declaration only, never copied, passed, returned, or
constructed by literal. Atomic operations accept **storage paths** as the
cell operand (`nodes[i].next`, `seqs[cell]`): identifier-rooted access
paths, emitted in checked lvalue position and addressed — never a
temporary. Deeper embeddings (cells inside ADT payloads, views/spans of
cells, generic arguments) remain rejected in v1. A future borrowed
`AtomicRef[T]` may transport cell identity without copying it; v1 does not
manufacture an implicit pointer or heap wrapper.

The canonical consumers are the 1024cores queue family: the intrusive
MPSC's atomic next links and the bounded MPMC's per-slot sequence cells.

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

Exchange (unconditional swap returning the prior value — the wait-free
RMW: one instruction, no retry; the Vyukov MPSC producer's claim):

```text
atomic_exchange_relaxed(cell, value) -> T
atomic_exchange_acquire(cell, value) -> T
atomic_exchange_release(cell, value) -> T
atomic_exchange_acq_rel(cell, value) -> T
atomic_exchange_seq_cst(cell, value) -> T
```

Fetch-add returns the pre-add value and exists for all five orders. Fences exist
for acquire, release, acq-rel, and seq-cst. Atomic exchange is a normative
source builtin: it is legal at every RMW order (the `rmw` row of
`Oak.MemoryOrder.legal`), carries the `Memory.AtomicRMW` effect, lowers to
`atomic_exchange_explicit`, and is exercised end to end by the zero-copy
receive path (`compiler/e2e_zero_copy_test.go`, `compiler/e2e_atomic_fields_test.go`).

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
backend/target implements every carrier lock-free, so the C backend makes the
target say so: for every atomic carrier the program declares storage for
(a named cell, a record field, an array element) the generated C ends with a
C99 static assertion that C11 atomics of that width are *always* lock-free
on the compiling target (`ATOMIC_{CHAR,SHORT,INT,LONG,LLONG}_LOCK_FREE == 2`,
consulted by width, so ILP32 and LP64 both read the macro that matches). A
target whose atomics fall back to a locked libatomic implementation — a
Cortex-M0+ compiling a `u32` fetch-add, for instance — fails the C build
instead of linking a hidden lock. A build that has audited the fallback and
accepts it defines `OAK_ATOMIC_ACCEPT_LOCKED`; that define is the "accepted
bounded implementation" and is visible in the build line, not in the
program. Under the strict profile the block has no opt-out: the
zero-warning posture reaches the C build (`85-discipline.md` §7). Carriers the program never declares are not asserted, so a
`u32`-only program still builds on a core without 64-bit exclusives.
(`codegen/memory.go` `emitAtomicAdmission`; `compiler/e2e_atomic_admission_test.go`
cross-compiles the same C for Cortex-M4, where it builds, and Cortex-M0+,
where the `u32` assertion fails and the define lifts it.)

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

The execution-level meaning is specified by the next three chapters:

- `66-memory-model.md`: reads-from, synchronizes-with, happens-before, conflicts,
  and data races;
- `67-memory-ordering.md`: modification order, RMW adjacency, release sequences,
  and fence-mediated synchronization;
- `68-sequential-consistency.md`: one explicit global SC order and SC-read
  visibility constraints.

Lean models these layers in `Oak.HappensBefore` and `Oak.SequentialConsistency`.
These are language-level proofs; C/ISA refinement remains a separate proof and
testing obligation.

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
- Semantic IR execution tests cover HB/race, modification order, release
  sequences, fences, and global SC validation;
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
| core happens-before/data-race relations | specified + implemented + Lean-modeled in chapter 66 |
| modification order/release sequences/fences | specified + implemented + Lean-modeled in chapter 67 |
| global seq-cst order/read visibility | specified + implemented + Lean-modeled in chapter 68 |
| language-level memory relation set | explicit through seq-cst |
| C refinement of the total arithmetic macros | proved: `Oak.ArithmeticRefinement` transliterates `OAK_ARITH_U`/`OAK_ARITH_I` and proves each body equal to the fixed-width operator; `codegen/arithmetic_refinement_test.go` pins the emitted text |
| order tables and builtin catalogue | correspondence: `Oak.MemoryOrderRefinement` decides the `legal`/`casLegal` tables and the 29-builtin catalogue, `semir/memory_refinement_test.go` pins the same against the Go decision procedures |
| strong compare-exchange helper | refinement: `Oak.CompareExchangeRefinement` proves the `__oak_cas_*` body meets §3's value contract over C11's primitive; `codegen/compare_exchange_refinement_test.go` pins the text |
| C/ISA refinement of atomics and ordering | not yet proved |
| AArch64 weak-memory litmus suite | next major layer |
| target lock-free admission (C backend) | implemented + cross-compile-tested (§6) |

The next work is no longer to invent additional language-level memory-order
semantics. It is to **refine and test the projection**: generated C, emitted
AArch64 instructions, and weak-memory litmus outcomes (target lock-free
admission is in place, §6). Higher-level SPSC/MPSC proofs should consume that demonstrated
compiler-to-machine contract rather than re-specifying atomics locally.

## Placement of statics

A static may declare its linker section with a placement clause after its
type — the clause form of `40-records.md` §6a, on a declaration:

```oak
ring: [8]u64 (section: ".shared")           // ELF
grant: [4096]u8 (section: "__DATA,grant")   // Mach-O: segment,section
```

The section name admits only `[A-Za-z0-9_.,$]`, so nothing but a plain
section spelling reaches generated C (`__attribute__((section(...)))`).
Fixed addresses are the linker script's job; only the section is language
surface. Together with `struct(align: N)`/`packed`, per-field `align`, and
`static_assert` over `size_of`/`offset_of`, this is the surface a ring or
grant window needs to live exactly where a stage-2 mapping expects it.
