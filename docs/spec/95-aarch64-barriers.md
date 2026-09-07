# AArch64 barriers: explicit ordering, completion, and instruction synchronization

This chapter defines Oak's first architecture-specific barrier surface for the
AArch64 operating-system profile.

The governing rule is:

> Barriers are explicit machine operations. Oak neither inserts them silently
> around volatile/MMIO accesses nor pretends they have portable host semantics.

The source spelling identifies the exact architectural operation and scope.
There is no runtime barrier enum, generic `barrier()` switch, hidden allocation,
or fallback to an unrelated host fence.

## 1. Source surface

The compiler-known `arm64` library exposes exactly these nullary functions:

```text
arm64.dmb_ishld() -> ()
arm64.dmb_ish()   -> ()
arm64.dmb_sy()    -> ()
arm64.dsb_ish()   -> ()
arm64.dsb_sy()    -> ()
arm64.isb()       -> ()
```

The option is part of the function identity. A program cannot construct a
runtime string/enum and ask the backend to choose a barrier dynamically.
Unknown barrier spellings fail type checking.

## 2. Semantic IR

`semir.Arm64BarrierSpec` records:

```text
member
operation  // DMB, DSB, ISB
scope      // ISHLD, ISH, SY, or none for ISB
```

and projects an explicit effect:

```text
Machine.Barrier[operation, scope?]
```

The catalog is the single source of barrier names for the typechecker and
verification tests. Semantic lookup is a static switch and is regression-tested
at zero allocations.

## 3. DMB, DSB, and ISB stay distinct

Oak intentionally does not collapse the three instruction families into a
single notion of "strong fence".

### 3.1 DMB

DMB is admitted as a data-ordering barrier in its selected domain. The Oak
profile does **not** claim DMB provides DSB-style completion.

`dmb_ishld` is a load-ordering profile and is intentionally weaker than the
full inner-shareable data barrier.

`dmb_ish` is the full inner-shareable data-ordering profile.

`dmb_sy` is the full system-scope data-ordering profile.

### 3.2 DSB

DSB provides the full data-ordering profile in the selected domain and adds the
completion property on which Oak machine code may rely.

`dsb_ish` is inner-shareable.

`dsb_sy` is system scope.

Oak does not automatically replace DMB with DSB "to be safe": unnecessary DSB
use can be materially more expensive and would obscure the intended hardware
contract.

### 3.3 ISB

ISB is modeled as instruction-context synchronization. It is not presented as a
substitute for DMB/DSB data ordering or completion.

Code that changes architectural state and requires an ISB must request
`arm64.isb()` explicitly.

## 4. Backend lowering

Each source barrier lowers through one `static inline` C helper whose AArch64
branch contains exactly one inline-assembly instruction:

```text
arm64.dmb_ishld -> dmb ishld
arm64.dmb_ish   -> dmb ish
arm64.dmb_sy    -> dmb sy
arm64.dsb_ish   -> dsb ish
arm64.dsb_sy    -> dsb sy
arm64.isb       -> isb
```

The inline assembly is `volatile` and carries a C compiler `"memory"` clobber.
That prevents the bootstrap C compiler from moving ordinary memory operations
through the explicit machine barrier in ways that would destroy Oak's intended
ordering boundary.

There is no Oak runtime call, heap object, dynamically selected instruction, or
hidden second barrier.

## 5. Fail closed outside AArch64

Unlike scalar value-transforming instruction functions such as byte-reverse or
CLZ, DMB/DSB/ISB do not have a faithful architecture-independent evaluator or C
fallback.

Therefore generated helpers contain a compile-time error when the AArch64
branch is unavailable.

A source program using:

```text
arm64.dsb_sy()
```

must not successfully compile for an ordinary x86 host merely because the
compiler can substitute a C atomic fence.

A C fence is not a semantic replacement for AArch64 DSB completion.

This fail-closed behavior is execution-tested with a host C compiler.

## 6. Reference evaluator

The Go evaluator recognizes barrier source functions and validates their arity,
but executing one returns an explicit error explaining that the operation
requires the native AArch64 backend.

The evaluator does **not**:

- silently return Unit;
- call Go atomics;
- insert a host mutex/fence;
- model DSB completion as sequential evaluation;
- pretend ISB has no observable semantic role.

This keeps interpretation honest: parsing/typechecking and native execution are
separate capabilities.

## 7. Allocation and performance contract

The barrier path is structurally minimal:

1. source operation identity is compile-time;
2. semantic catalog lookup performs zero allocations;
3. typechecking has no runtime barrier object;
4. generated code contains one inline helper per barrier actually used;
5. helper body contains one barrier instruction in the AArch64 branch;
6. no Oak heap allocation, callback, table dispatch, or syscall exists on the
   runtime path;
7. unused barrier helpers are not emitted.

This is intended to make privileged hot paths reviewable directly from source
and assembly.

## 8. Formal verification

`spec/lean/Oak/AArch64Barrier.lean` defines a deliberately narrow capability
model rather than attempting to reproduce the full Arm memory axiomatic model.

It distinguishes:

```text
data ordering: none / load / full
completion
instruction synchronization
scope: inner-shareable / system
```

Lean proves:

- admitted DMB variants do not claim completion;
- admitted DSB variants do claim completion;
- data barriers do not claim instruction-stream synchronization;
- ISB does claim instruction synchronization;
- DSB ISH preserves the full DMB ISH data-ordering class and adds completion;
- DSB SY likewise extends DMB SY with completion;
- DMB ISHLD is not classified as a full data barrier;
- ISB makes no DMB/DSB-style data-order/completion claim.

These are Oak profile facts, not a formal proof of every Arm architectural
behavior.

## 9. End-to-end verification

The slice is accepted only if all of the following hold:

- SemIR catalog/effect/instruction-spelling tests pass;
- SemIR lookup remains zero-allocation;
- typechecker accepts every exact nullary barrier and rejects operands/unknown
  spellings;
- evaluator diagnoses every barrier as native-AArch64-only;
- Oak-generated C contains no heap primitive in the barrier path;
- Clang cross-compiles the generated source for freestanding ARMv8-A;
- each Oak function contains the exact requested DMB/DSB/ISB instruction and no
  additional barrier family;
- the same source fails closed when compiled by an ordinary host C compiler;
- Lean kernel-checks the capability model;
- ordinary Go/race, golden, and AArch64-refinement CI remain green.

## 10. Relationship to atomics and volatile access

Barriers are not replacements for the atomic model in chapters 65–69.

Likewise, volatile access means an observable access occurs; it does not imply a
DMB, DSB, ISB, acquire, release, or device-completion contract.

Oak deliberately keeps:

```text
volatile access
atomic synchronization
AArch64 barrier
```

as separate concepts that may be composed explicitly when hardware semantics
require them.

This matters for MMIO: the correct barrier depends on the device protocol,
memory attributes, DMA/coherency rules, and the operation being performed.
Automatically inserting a maximal barrier around every register access would
be both semantically imprecise and unnecessarily slow.

## 11. Verification status

| Layer | Status |
| --- | --- |
| exact source barrier catalog | specified + implemented |
| Semantic IR barrier operation/scope/effect | specified + implemented + tested |
| nullary source typing | implemented + tested |
| zero-allocation semantic lookup | regression-tested |
| native AArch64 inline-asm lowering | implemented + assembly-tested |
| fail-closed non-AArch64 lowering | implemented + execution-tested |
| evaluator honesty/native requirement | implemented + tested |
| barrier capability classification | Lean-modeled + proved |
| full formal Arm axiomatic refinement | not claimed |
| typed MMIO register/address model | next |
| device memory attributes | not yet modeled |
| DMA/coherency ordering | not yet modeled |

## 12. Next layer: typed MMIO

The next machine slice should introduce nominal register-address types such as:

```text
mmio.U8
mmio.U16
mmio.U32
mmio.U64
```

with explicit unsafe construction from an address, width/alignment validation,
and exact one-access volatile read/write functions.

No MMIO read/write will insert a barrier automatically. Device drivers and
hypervisor adapters will compose typed MMIO operations with the barrier contract
in this chapter according to the hardware protocol they implement.
