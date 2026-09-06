# Machine memory: atomics, volatile access, and ordering

This chapter specifies Oak's first executable machine-memory contract. It is
small on purpose: fixed-width integer atomic cells, explicit memory order,
allocation-free source operations, and raw volatile access. Device MMIO,
architecture barriers, system registers, and inline assembly build on this
layer but remain separate contracts.

The governing rule is:

> Memory effects that matter to hardware or concurrency are language semantics,
> never backend accidents.

## 1. Atomic cells

`Atomic[T]` is storage identity for one atomically accessed machine cell.
Atomicity belongs to the cell and its accesses; a value loaded from
`Atomic[u32]` is an ordinary `u32`.

The v1 carriers are exactly:

- `u8`, `u16`, `u32`, `u64`;
- `i8`, `i16`, `i32`, `i64`.

`int`, `uint`, `ptr`, `uptr`, booleans, records, sums, and aggregates are not
v1 atomic carriers. Pointer atomics require a provenance contract; native-width
integers require a target-width contract; aggregate atomics require explicit
layout and lock-freedom rules. Oak does not infer any of those contracts.

A source cell is declared directly:

```text
counter: Atomic[u64]
```

A v1 `Atomic[T]` declaration has no initializer. The cell is zero-initialized
and must subsequently be changed with an explicit atomic store/RMW operation.
This keeps construction deterministic and prevents an ordinary write from
being confused with an atomic publication operation.

### 1.1 Storage identity and non-copy rules

`Atomic[T]` is not an ordinary copyable value in v1. The following are rejected:

- direct assignment to an atomic cell;
- copying/inference from an atomic cell into another value binding;
- ordinary arithmetic, comparison, matching, or prefix operations on the cell;
- passing an atomic cell by value to a function;
- returning an atomic cell by value;
- embedding atomic storage in arrays, records, ADT payloads, or generic values.

Atomic source operations require a named cell as their first operand. A loaded
or RMW-returned value is the ordinary carrier `T` and can then participate in
normal value semantics.

This restriction is deliberate. A future `AtomicRef[T]`/borrowed-place contract
may permit safe transport of cell identity without copying storage, but v1 does
not manufacture an implicit pointer or wrapper to make that appear to work.

## 2. Memory orders

Oak defines exactly five memory orders:

- `relaxed`;
- `acquire`;
- `release`;
- `acq-rel`;
- `seq-cst`.

The order is part of the operation's semantics and is retained in Semantic IR
effects. Backends may not silently weaken, strengthen, or guess an order.

The legality matrix is:

| Operation | relaxed | acquire | release | acq-rel | seq-cst |
| --- | --- | --- | --- | --- | --- |
| load | yes | yes | no | no | yes |
| store | yes | no | yes | no | yes |
| read-modify-write | yes | yes | yes | yes | yes |
| fence | no | yes | yes | yes | yes |

A release load, acquire store, and relaxed fence are not merely rejected at
runtime: the v1 source surface has no constructor for them.

## 3. Normative v1 source surface

Order is encoded in the builtin name. There is no runtime order enum, no
implicit default, and no order-dispatch branch in generated code.

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

Fetch-add read-modify-write operations return the value that existed before the
addition:

```text
atomic_fetch_add_relaxed(cell, delta) -> T
atomic_fetch_add_acquire(cell, delta) -> T
atomic_fetch_add_release(cell, delta) -> T
atomic_fetch_add_acq_rel(cell, delta) -> T
atomic_fetch_add_seq_cst(cell, delta) -> T
```

Fences:

```text
atomic_fence_acquire() -> ()
atomic_fence_release() -> ()
atomic_fence_acq_rel() -> ()
atomic_fence_seq_cst() -> ()
```

Compare-exchange is intentionally deferred. It has independent success/failure
orders, restrictions on failure order, and expected-value update semantics.
Oak will specify those facts directly instead of pretending compare-exchange is
a one-order RMW.

Atomic exchange remains a backend/Semantic-IR building block but is not part of
the normative v1 source surface in this chapter.

## 4. Effects and semantic authority

Atomic operations project into Oak's authority/effect axis:

```text
Memory.AtomicLoad[order]
Memory.AtomicStore[order]
Memory.AtomicRMW[order]
Memory.AtomicFence[order]
```

The compiler uses one semantic builtin descriptor for source identity, arity,
operation class, order, result shape, effect projection, type checking, and
backend lowering. Verification and implementation therefore do not maintain
independent order tables that can silently drift.

Atomic operations do not semantically imply allocation, blocking, scheduler
interaction, I/O, or syscalls.

## 5. Allocation and performance contract

The v1 performance contract is structural rather than aspirational:

1. an `Atomic[T]` cell lowers to inline `_Atomic(T)` storage;
2. an atomic operation allocates no Oak heap object;
3. memory order is compile-time data, not a runtime parameter;
4. each source load/store/fetch-add/fence lowers directly to the corresponding
   explicit C11 primitive rather than an Oak runtime wrapper;
5. the compiler's atomic-builtin semantic lookup allocates zero objects per
   lookup (regression-tested with `testing.AllocsPerRun`);
6. `<stdatomic.h>` is emitted only when the program actually uses atomics, so
   non-atomic generated C remains unchanged;
7. generated atomic C is checked for accidental `malloc`, `calloc`, `realloc`,
   `free`, or runtime order-switch scaffolding.

These rules eliminate language/runtime overhead around the machine primitive.
They do **not** claim that every C target implements every `_Atomic(T)` without
an internal library lock. Lock-freedom is a target property. A freestanding or
hard-realtime target profile must separately establish the required carrier is
lock-free before relying on a bounded atomic WCET.

Correctness takes precedence over an unsupported lock-free claim.

## 6. C bootstrap backend

The bootstrap C backend refines Oak atomics to C11 `_Atomic(T)` and explicit
`atomic_*_explicit` operations with the exact corresponding `memory_order_*`.
It uses the fixed-width Oak carrier rather than an implementation-sized atomic
convenience typedef.

The mapping is checked and total. An unknown Oak order, illegal operation/order
pair, temporary cell operand, or unsupported carrier fails closed rather than
falling back to a weaker or stronger operation.

For example:

```text
atomic_fetch_add_relaxed(counter, u64(1))
```

lowers directly to the semantic equivalent of:

```c
atomic_fetch_add_explicit(&(counter), (u64)1, memory_order_relaxed)
```

The C atomic dependency is pay-for-use: non-atomic programs do not include
`<stdatomic.h>`.

## 7. Reference evaluator

The Go evaluator represents an Oak atomic declaration as one persistent
`sync/atomic.Int64` cell object and mutates that cell in place. It is a
reference for storage identity and value semantics, including fetch-add's
old-value result.

Go's atomic operations are stronger than several Oak order variants, so the
evaluator is **not** a weak-memory litmus engine and is not used to validate the
precise acquire/release/relaxed distinctions. Exact order refinement is tested
through generated C11 code and is modeled separately in Lean.

## 8. Volatile access

Volatile access means the requested load or store is an observable machine
access and must not be removed, duplicated, merged, or satisfied from a cached
language value in a way that changes the required observable access.

The effects are:

```text
Memory.VolatileRead
Memory.VolatileWrite
```

Volatile is **not** an atomic synchronization primitive, a replacement for
acquire/release atomics, or by itself a complete device-MMIO ordering contract.

This distinction is essential on weakly ordered architectures including
AArch64. Device-memory type, access width, barriers, and architecture-specific
ordering rules belong to the MMIO/architecture layer built above this one.
Raw volatile C lowering intentionally emits no hidden fence.

## 9. Formal verification

`spec/lean/Oak/MemoryOrder.lean` is the kernel-checked projection of the v1
legality matrix and exact source builtin set. It proves:

- release and acq-rel loads are illegal;
- acquire and acq-rel stores are illegal;
- every defined order is legal for RMW operations;
- relaxed fences are illegal;
- legal loads cannot have release/acq-rel ordering;
- legal stores cannot have acquire/acq-rel ordering;
- **every source builtin maps to a legal `(operation, order)` pair**;
- the source surface cannot express release/acq-rel loads;
- the source surface cannot express acquire/acq-rel stores;
- the source surface cannot express a relaxed fence.

These proofs establish the language-level order/surface contract. They do not
prove that a particular C compiler or ISA implements the entire Oak memory
model; that stronger backend/ISA refinement remains a later layer.

## 10. End-to-end implementation tests

The executable v1 slice is tested across all current layers:

- parser: `Atomic[T]` and order-specific builtin calls parse as ordinary Oak
  syntax without special parser magic;
- typechecker: valid calls return the carrier/unit type and invalid carriers,
  copied cells, initializers, by-value transport, temporary operands, and wrong
  value types are rejected;
- Semantic IR: every source builtin is checked against the same legality/effect
  descriptor and the lookup is zero-allocation;
- evaluator: cell identity, store/load, fetch-add old-value semantics, and
  direct-assignment rejection are executed;
- backend: generated C contains exact C11 explicit atomics and no hidden
  allocation/runtime order dispatch;
- pay-for-use: a non-atomic source program does not acquire the C atomic header
  or atomic storage;
- native execution: generated C is compiled with C11 and pthreads, four host
  threads perform 100,000 contended Oak-generated relaxed fetch-add operations,
  and an acquire load verifies the exact final count;
- repository regression: the complete Go suite is run with the Go race detector
  and the existing golden corpus remains unchanged for non-atomic programs;
- Lean: the abstract legality matrix and exact source surface are kernel-checked.

This is the acceptance bar for calling the v1 source atomic slice implemented,
not merely scaffolded.

## 11. Verification status and remaining layers

For the source atomic slice in this chapter:

| Layer | Status |
| --- | --- |
| normative source/storage semantics | specified |
| order matrix | proved in Lean |
| exact source builtin legality | proved in Lean |
| parser/typechecker/evaluator | implemented and tested |
| C11 source refinement | implemented and execution-tested |
| compiler-path allocation regression | tested at zero allocations |
| native contended RMW correctness | execution-tested |
| C/ISA formal refinement | not yet proved |
| weak-memory architecture litmus suite | not yet implemented |
| hardware-specific lock-free admission | not yet implemented |

The remaining concurrency/machine contracts include:

- compare-exchange;
- pointer atomics and provenance;
- wait/notify primitives;
- the complete non-atomic data-race and happens-before model;
- compiler-reordering refinement beyond the atomic primitives;
- AArch64 barrier selection and weak-memory litmus tests;
- device-memory attributes/MMIO ordering;
- DMA coherency and interrupt-entry ordering;
- freestanding linker/ABI rules.

Those contracts must remain explicit before Oak owns the corresponding
privileged operating-system mechanisms.
