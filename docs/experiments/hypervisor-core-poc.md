# Hypervisor Core Proof-of-Concept

## Purpose

This experiment tests Oak against real requirements from the hypervisor-first OS rather than adding language features in the abstract.

The question is not yet whether Oak can replace Zig. The question is whether one Oak-oriented semantic description can increasingly support:

```text
systems implementation
formal proof
boundedness checking
machine representation
protocol modeling
property / integration tests
future debugger metadata
```

without duplicating facts or hiding machine cost.

## Current slices

### Virtual interrupt semantics

`semir/ir_test.go::TestIrqDefinitionsExerciseFiveAxes` already demonstrates the five-axis Semantic IR using `IrqId`, IRQ representation/authority/effects, and a `VirtualIrq` protocol.

`compiler/hypervisor_poc_test.go::TestHypervisorPOCVirtualIrqLifecycle` adds an executable Oak slice. It models an edge-triggered IRQ lifecycle with:

```text
Disabled
Idle
Pending
Active
ActivePending
```

`ActivePending` preserves an edge arriving while an interrupt is active. EOI then exposes that edge as `Pending` rather than losing it.

`Oak.HypervisorPOC.edge_while_active_repends` proves the corresponding abstract law in Lean.

### Bounded priority selection

`TestHypervisorPOCBoundedIrqSelection` performs priority selection over fixed caller-owned arrays/spans.

The POC deliberately requires Oak's `strict` discipline profile:

- fixed storage;
- no hidden allocation;
- no recursion;
- statically recognized bounded loop;
- bounds-checked span reads/writes;
- deterministic lowest-priority-value selection under the mask.

This is a first proxy for the OS requirement that the IRQ hot path be simple, bounded, cache-small, and mechanically analyzable.

The Lean `Deliverable` predicate proves the local facts that a deliverable interrupt is enabled, pending, inactive, and below the priority mask. A later step should prove the concrete selection algorithm returns the minimum-priority deliverable IRQ and then refine the executable implementation to that model.

### Stage-2 page arithmetic

`TestHypervisorPOCStageTwoPageArithmetic` executes 4 KiB page base/index/offset calculations and checks reconstruction with always-on assertions.

The Lean model proves:

- page bases are granule-aligned;
- page offsets are in range;
- base + offset reconstructs the address;
- page base equals page index times page size.

The current Lean model uses mathematical naturals. This is **not yet** a proof of Oak `u64` lowering: fixed-width overflow/division/conversion semantics and their implementation refinement remain a separate machine-integer obligation.

### Generational handles

`Oak.HypervisorPOC.stale_handle_fails_after_reuse` proves the basic stale-generation law used by capability/object handles. This complements the existing, more general `Oak.Handles` work.

The finite-width production policy remains: generation exhaustion retires a slot rather than wrapping and accidentally reviving stale authority.

## Verification levels

For this experiment we distinguish the following strictly:

```text
Semantic IR modeled       yes, for the IRQ five-axis example
Oak executable code       yes, for IRQ lifecycle/selection and page arithmetic
Strict discipline checked yes
C lowering                yes when compiler CI passes
Native host execution     yes when compiler CI passes
Lean abstract laws        yes when formal CI passes
Implementation refinement no
AArch64 EL2 integration   no
```

A green Lean build proves the theorems in `Oak.HypervisorPOC`; it does not prove the generated C implements those theorems. A green compiler test proves the current implementation accepted/lowered/executed the POC; it does not by itself establish formal correspondence.

## Next machine-facing experiments

The next useful POCs should be driven by actual EL2 needs:

1. fixed-width machine-integer semantics/refinement for page-table arithmetic;
2. explicit packed/extern/offset representation suitable for architectural descriptors;
3. atomics and memory-order semantics with a formal memory model;
4. volatile/MMIO plus AArch64 barrier effects;
5. system-register and constrained inline-assembly/intrinsic boundaries;
6. freestanding C/object emission with no libc/runtime dependency;
7. a real Oak-generated pure IRQ object linked into the existing Zig/QEMU EL2 payload;
8. protocol projection to a temporal model and generated deterministic-simulation actions.

Oak should replace a piece of Zig only after that piece is demonstrably at least as controllable at the machine level and has a stronger correctness story.
