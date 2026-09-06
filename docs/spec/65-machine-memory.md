# Machine memory: atomics, volatile access, and ordering

This chapter specifies Oak's machine-memory foundation. It is deliberately
small: fixed-width integer atomics, explicit memory order, and raw volatile
access. Device MMIO, architecture barriers, system registers, and inline
assembly build on this layer but are separate contracts.

The governing rule is:

> Memory effects that matter to hardware or concurrency are language semantics,
> never backend accidents.

## 1. Atomic values

`Atomic[T]` is the semantic type of one atomically accessed machine value.
Atomicity belongs to the cell and its accesses; a value loaded from
`Atomic[u32]` is an ordinary `u32`.

The first executable version permits only fixed-width integer carriers:

- `u8`, `u16`, `u32`, `u64`
- `i8`, `i16`, `i32`, `i64`

`int`, `uint`, `ptr`, `uptr`, booleans, records, sums, and aggregates are not
v1 atomic carriers. Pointer atomics require a provenance contract; native-width
integers require a target-width contract; aggregate atomics require explicit
layout and lock-freedom rules. Those are not inferred implicitly.

A target may impose stronger alignment than the carrier's ordinary alignment.
Whether a particular `Atomic[T]` is lock-free is a target property. Oak must
not claim lock-free execution unless the selected target/backend proves or
checks it.

## 2. Memory orders

Oak defines exactly five memory orders:

- `relaxed`
- `acquire`
- `release`
- `acq-rel`
- `seq-cst`

The order is part of the operation's semantics and is preserved in Semantic
IR effects. Backends may not silently weaken, strengthen, or guess an order.

The v1 legality matrix is:

| Operation | relaxed | acquire | release | acq-rel | seq-cst |
| --- | --- | --- | --- | --- | --- |
| load | yes | yes | no | no | yes |
| store | yes | no | yes | no | yes |
| read-modify-write | yes | yes | yes | yes | yes |
| fence | no | yes | yes | yes | yes |

A release load and acquire store are language errors. A relaxed fence is not a
surface operation because it creates no synchronization relation.

## 3. Initial operation set

The first machine-memory slice supports semantic lowering for:

- atomic load
- atomic store
- atomic exchange
- atomic fetch-add
- thread fence

Compare-exchange is intentionally deferred. It has separate success and failure
orders, restrictions on the failure order, and value-update semantics. Oak will
specify those directly instead of pretending compare-exchange is a one-order
RMW.

The eventual source surface should make the order explicit at the call site.
The exact spelling is not normative until parser/typechecker integration lands.
The semantic shape is equivalent to:

```text
atomic_load(cell, acquire)
atomic_store(cell, value, release)
atomic_exchange(cell, value, acq_rel)
atomic_fetch_add(cell, delta, relaxed)
atomic_fence(seq_cst)
```

There is no implicit default order in the core language.

## 4. Effects

Atomic operations project into Oak's authority/effect axis:

```text
Memory.AtomicLoad[order]
Memory.AtomicStore[order]
Memory.AtomicRMW[order]
Memory.AtomicFence[order]
```

The order parameter is semantic data. Proof generation, documentation,
debugging, realtime analysis, and future temporal projections can therefore
reason about synchronization without reparsing source syntax.

Atomic operations do not imply allocation, blocking, scheduler interaction, or
syscalls.

## 5. Volatile access

Volatile access means that the requested load or store is an observable machine
access and must not be removed, duplicated, merged, or satisfied from a cached
language value in a way that changes the required observable access.

The effects are:

```text
Memory.VolatileRead
Memory.VolatileWrite
```

Volatile is **not** an atomic synchronization primitive.
Volatile is **not** a replacement for acquire/release atomics.
Volatile is **not** by itself a complete device-MMIO ordering contract.

This distinction is essential on weakly ordered architectures, including
AArch64. Device-memory type, access width, barriers, and architecture-specific
ordering rules belong to the MMIO/architecture layer built above this one.

## 6. C bootstrap backend

The bootstrap C backend refines Oak atomics to C11 `_Atomic(T)` and explicit
`atomic_*_explicit` operations with the corresponding `memory_order_*` value.
It uses the fixed-width Oak carrier rather than an implementation-sized atomic
convenience typedef.

The mapping is checked and total. An unknown Oak order or illegal
operation/order pair is a backend error rather than a fallback.

Raw volatile lowering uses `volatile T *` access and emits no hidden fence.
Any future MMIO primitive that requires barriers must request them explicitly
through the machine/architecture semantics.

## 7. Formal model

`spec/lean/Oak/MemoryOrder.lean` is the kernel-checked projection of the v1
legality matrix. It proves, among other facts:

- release and acq-rel loads are illegal;
- acquire and acq-rel stores are illegal;
- every defined order is legal for RMW operations;
- relaxed fences are illegal;
- legal loads cannot have release/acq-rel ordering;
- legal stores cannot have acquire/acq-rel ordering.

These proofs establish the abstract order contract. They do not yet prove that
the C compiler, target ISA, or generated machine code implements the full Oak
memory model. That stronger refinement is a later verification layer.

## 8. What this chapter does not yet claim

This slice is the foundation, not the completed concurrency model. It does not
yet specify:

- compare-exchange;
- pointer atomics;
- wait/notify primitives;
- data-race semantics for non-atomic memory;
- compiler reordering outside atomic operations;
- a complete happens-before relation;
- architecture-specific barrier selection;
- device-memory attributes or MMIO ordering;
- DMA coherency;
- interrupt-entry ordering;
- freestanding linker/ABI rules.

Those contracts must be explicit before Oak owns privileged operating-system
code.

## 9. Required verification ladder

Machine-memory features are complete only when their status is stated at each
layer:

1. **specified** — normative semantics are written here;
2. **modeled/proved** — Lean/TLA/other formal artifacts establish the intended
   laws;
3. **implemented** — typechecker and backend expose the operation end-to-end;
4. **implementation-tested** — generated code is compiled and executed;
5. **refined** — the backend/target mapping is related formally to the language
   model where practical;
6. **hardware-tested** — litmus tests exercise the target architecture.

The current first slice establishes the semantic model, checked type/backend
building blocks, tests, and Lean order proofs. Source syntax and full
end-to-end atomic execution are the next step.
