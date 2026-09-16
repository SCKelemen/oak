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

DSB provides the full data-ordering profile in the selected domain. Oak's
barrier capability also records the architectural completion obligation on
which machine code may rely once an execution-level Arm refinement discharges
it.

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

### 3.4 TLBI is translation maintenance, not a fourth barrier

The adjacent closed operation:

```text
arm64.tlbi_vmalls12e1is() -> ()
```

names exactly `TLBI VMALLS12E1IS`. It lives in a separate
`semir.Arm64TLBISpec` catalog and projects
`Machine.TranslationMaintenance[tlbi, vmalls12e1, inner-shareable]`, never a
`Machine.Barrier` capability. It does not insert or imply a preceding or
following DSB or ISB. Any required surrounding DSB or ISB must be spelled
separately, and the protocol must discharge its applicable ordering,
completion, and context-synchronization obligations.

The source identity deliberately includes `is`: a future plain, local-PE
`TLBI VMALLS12E1` operation would require a distinct catalog member. Runtime
instruction or scope operands are not accepted.

### 3.5 Fixed VMALLS12E1IS context-sync slice

The reference leaf
`examples/hypervisor/stage2_vmalls12e1is_context_sync.oak` spells this fixed
sequence in Oak source:

```text
DSB ISH
TLBI VMALLS12E1IS
DSB ISH
ISB
```

It is an IS-only maintenance/context-synchronization slice, not a compound
intrinsic or a complete break-before-make protocol. Descriptor break/make,
target and scope suitability, completion, and context synchronization remain
protocol proof obligations. The initial DSB ISH is deliberately conservative;
the existence of this fixed leaf is not a claim that it is cheaper than every
protocol-specific sequence that can justify a narrower barrier. Callers that
do not require context synchronization should continue to spell only the
operations their proof requires rather than pay for an unconditional ISB.

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

The TLBI helper uses the same `volatile`/`"memory"` form, and the direct-native
scheduler and memory-value forwarder keep TLBI as an immovable compiler
boundary. These are compiler-ordering constraints only. They are not DSB
ordering, invalidation completion, or evidence about architectural broadcast.

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

Lean proves these facts about Oak's profile capability record:

- admitted DMB variants do not claim completion;
- admitted DSB variants do claim completion;
- data barriers do not claim instruction-stream synchronization;
- ISB does claim instruction synchronization;
- DSB ISH preserves the full DMB ISH data-ordering class and adds completion;
- DSB SY likewise extends DMB SY with completion;
- DMB ISHLD is not classified as a full data barrier;
- ISB makes no DMB/DSB-style data-order/completion claim.

`Oak.AArch64Encoding` and the generated Sail bridge refine the six literal
instruction words into these exact capabilities through Arm's decoded
operation/domain/access tuple. The decoded DMB ISHLD/ISH/SY tuples index the
restricted weak-memory `bob` rule: ISHLD orders only a returning load before
following scalar memory, while ISH and SY provide full scalar data ordering.
Decoded DSB ISH/SY tuples index a separate full scalar `DSB-ob` rule. The pinned
CAT certificate covers `dmb.full`, `dmb.ld`, the selected `bob` arms,
`dsb.full`, the full scalar `DSB-ob` arm, ISB membership in `IFB`, a
dependency-sensitive `IFB-ob` arm, and their routes through `lob`. DSB and ISB
are not smuggled through DMB ordering. Eleven official-model Herd cases include
forbidden DSB ISH/SY store buffering and allowed bare-ISB store buffering.

Oak's pure Sail fragment projects barrier decoding to the
operation/domain/access tuple and now separately projects the official
`system_barriers` call target. The Lean bridge kernel-proves that the exact ISB
word selects `InstructionSynchronizationBarrier` in this local projection; a
Go drift gate audits all six mappings against the pinned official Sail source.
The projection does not execute architectural state changes: the pinned model
implements `InstructionSynchronizationBarrier` and `SynchronizeContext` as
separate unit-returning stubs. The drift gate pins that boundary. DSB completion
and ISB context synchronization therefore remain external obligations;
positive `IFB-ob` also requires its specified dependency.

`compiler/e2e_native_barrier_words_test.go` independently checks occurrence at
the direct-native object seam. Each of six Oak source functions must be exactly
one literal barrier word followed by `RET`; the expectation is not computed by
the encoder being tested. The same gate pins the actual cold prepare/entry
functions through their eight context writes, exact ISB, and final `RET` or
`ERET`. This is executable compiler evidence, not an Arm execution-semantics
proof and not the source of the word-to-decoder theorem.

The same object seam separately requires an Oak
`arm64.tlbi_vmalls12e1is()` leaf to contain exactly `0xd50c83df; RET`.
`Oak.AArch64Encoding` proves the word from the generated fields, and the Sail
bridge proves the named call target in Oak's pure projection. The object check
proves neither access admission nor the target's execution effects.

The fixed context-sync leaf is separately required to be exactly
`DSB ISH; VMALLS12E1IS; DSB ISH; ISB; RET` in the direct-native object. The C
bootstrap assembly gate requires the same four system instructions in order.
These gates establish emitted occurrence/order and zero hidden work, not DSB
completion or ISB architectural context synchronization.

These are Oak profile facts, not a formal proof of every Arm architectural
behavior.

## 9. End-to-end verification

The slice is accepted only if all of the following hold:

- SemIR catalog/effect/instruction-spelling tests pass;
- SemIR lookup remains zero-allocation;
- typechecker accepts every exact nullary barrier and rejects operands/unknown
  spellings;
- evaluator diagnoses every barrier as native-AArch64-only;
- the evaluator likewise diagnoses TLBI as native-AArch64-only rather than a
  no-op or host fence;
- Oak-generated C contains no heap primitive in the barrier path;
- Clang cross-compiles the generated source for freestanding ARMv8-A;
- each Oak function contains the exact requested DMB/DSB/ISB instruction and no
  additional barrier family;
- direct-native object bodies contain the independently pinned exact word with
  no prologue, dispatch, or second instruction before `RET`;
- the exact TLBI leaf is `0xd50c83df; RET`, and compiler scheduling/value
  forwarding cannot cross the TLBI occurrence;
- the fixed context-sync leaf contains exactly the two DSB words, IS TLBI word,
  ISB word, and `RET`, while its C lowering preserves the four-operation order;
- the same source fails closed when compiled by an ordinary host C compiler;
- Lean kernel-checks the capability model;
- the generated Sail decoder refines all six words into those capabilities,
  the three decoded DMB forms into restricted weak-memory ordering, and both
  decoded DSB forms into the separate full scalar ordering;
- pinned Herd tests cover DMB SY, DSB ISH/SY, bare ISB, and both the ordering
  and non-ordering directions of DMB ISHLD;
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
