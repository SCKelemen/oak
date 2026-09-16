# EL2 cold guest entry

Status: executable reference protocol for first entry into a guest stage-2 context.

## Purpose

This protocol extends the cold preparation sequence with the architectural exception return that actually transfers execution to the guest.

Reference implementation:

```text
examples/hypervisor/el2_cold_enter.oak
```

It is intentionally a **cold-entry** protocol. The target vCPU/stage-2 context must not previously have executed under the VTTBR/VTCR configuration being installed here.

Live reconfiguration of an active stage-2 context is outside this contract and requires an explicit translation-invalidation protocol with the architecturally required DSB/TLBI/ISB sequence.

## Source contract

The reference function has type:

```oak
fn el2_cold_enter(...) -> never
```

The sequence is:

1. execute `arm64.daifset_irq()`; on access-admitted execution its `#2`
   operand sets `PSTATE.I`;
2. install `HCR_EL2`;
3. install `VTTBR_EL2`;
4. install `VTCR_EL2`;
5. install `CNTHCTL_EL2`;
6. install `CNTVOFF_EL2`;
7. install guest `SP_EL1`;
8. install guest PC in `ELR_EL2`;
9. install guest PSTATE in `SPSR_EL2`;
10. execute explicit `ISB`;
11. execute `ERET`.

`ERET` is the terminal expression and the function cannot return normally.

## Preconditions and trust boundary

This protocol proves and tests the **shape and ordering** of the control-transfer sequence. It does not prove that arbitrary caller-provided register bit patterns are architecturally valid.

The caller is responsible for supplying values satisfying the relevant architecture constraints, including:

- a valid `HCR_EL2` configuration for the intended guest mode;
- valid `VTTBR_EL2` and `VTCR_EL2` values for the installed stage-2 tables;
- valid timer virtualization controls;
- a valid EL1 stack pointer and guest entry PC;
- an `SPSR_EL2` value selecting the intended exception level/state and interrupt mask policy.

Future typed register/configuration builders should move these obligations from caller assumptions into construction-time proofs and refinement checks.

## Ordering and synchronization

The register writes are explicit machine effects. Their compiler helpers carry a compiler `memory` clobber so the C bootstrap backend cannot freely reorder surrounding memory operations, but that clobber is **not** an architectural barrier.

The protocol therefore contains the required visible `ISB` before `ERET`. Neither system-register writes nor `ERET` silently add DMB/DSB/ISB operations.

This cold-entry contract intentionally contains no `DMB` or `DSB`. That is not a general statement about stage-2 maintenance; active translation-context changes require their own explicit invalidation/completion protocol.

## Allocation and performance

The path must be suitable for privileged execution:

- no heap allocation;
- no runtime opcode/register dispatch;
- no callback or virtual-dispatch chain;
- register and instruction identities are compile-time constants;
- generated code is a straight-line sequence of machine operations ending in `ERET`.

The assembly acceptance test rejects references to `malloc`, `calloc`, `realloc`, and `free`, and rejects an ordinary `RET` path.

## Formal model

`Oak.AArch64ColdEntry.ProtocolStep` models the shape-only protocol stages:

```text
start
 -> irqMasked
 -> executionConfigured
 -> stageTwoConfigured
 -> timerConfigured
 -> guestContextInstalled
 -> synchronized
 -> transferred
```

The evidence-bearing `Oak.AArch64ColdEntry.Step` is occurrence-indexed. Its
`ContextSyncWitness` carries:

- one exact occurrence for each of the eight required system-register writes;
- one exact `AArch64Encoding.isbSy` occurrence after every write;
- an explicit external `ArmContextSync` proof for that ISB occurrence.

`Step.eret` separately carries the exact ERET occurrence/action and its
program-order edge after that same retained ISB witness.

The generated Sail bridge refines such a witness with a kernel proof that the
exact ISB word selects `InstructionSynchronizationBarrier` in Oak's local pure
projection. A Go drift gate audits that projection against the pinned official
Sail source. The refinement is a conjunction and retains the original external
`ArmContextSync`; it cannot construct synchronization evidence from dispatch
identity.

The Lean model proves:

- shape-only transfer can occur only from `synchronized`;
- evidence-bearing transfer exposes the retained synchronization witness,
  exact ERET occurrence, and ISB-before-ERET edge;
- every required context write precedes ERET by transitivity;
- `transferred` is terminal in the cold-entry protocol.

`ArmContextSync` remains an explicit parameter until an Arm execution/state
model with non-erased context effects discharges it. It is not derived from the
barrier capability Boolean, pure decoding/dispatch, or CAT ordering. Caller
register values also remain outside these protocol-order proofs. Only the eight
writes, ISB, and ERET are occurrence-classified here; DAIFSet and the remaining
phase transitions are still shape-only.

Independently, `Oak.AArch64Encoding` computes the static DAIFSet word as
`0xd50342df`, and the generated Sail bridge proves that successful dispatch
with operand `#2` runs a D/A/I/F body that sets I and preserves D/A/F. This
does not supply the missing `Step.maskIrq` occurrence, discharge access/trap
checks, or prove maskable IRQ delivery remains disabled over the interval.

The next theorem computes static `MSR HCR_EL2, X0` word `0xd51c1100` and
proves the generated pure component body takes Arm's direct HCR_EL2 assignment
at EL2. It retains the EL1 redirect predicate over old HCR and SCR bit
projections without modeling NVMem(120). It proves no access/trap admission,
old-bit-to-old-value consistency, runtime X0 provenance, valid HCR
configuration, stage-2 enablement, exception routing, observation by later
writes, or dynamic occurrence.

The adjacent VTTBR theorem computes static `MSR VTTBR_EL2, X1` word
`0xd51c2101` and proves the generated pure component body takes Arm's direct
VTTBR_EL2 assignment at EL2. It retains the distinct EL1 nested-virtualization
redirect. This does not prove access/trap admission, runtime X1 value
provenance, valid VTTBR fields, table publication, or dynamic occurrence.

The following VTCR theorem computes static `MSR VTCR_EL2, X2` word
`0xd51c2142`. The pinned Arm model declares VTCR_EL2 as 32-bit, and generated
Lean proves the direct EL2 body installs exactly X2 bits 31:0. Its EL1 redirect
records unchanged VTCR_EL2 while the official source assigns NVMem(64). This
does not prove access/trap admission, runtime X2 provenance, upper-bit
preservation, valid VTCR fields, VTTBR compatibility, ordering, or occurrence.

The timer-control theorem computes static `MSR CNTHCTL_EL2, X3` word
`0xd51ce103`. Generated Lean proves the exact target and the official admitted
body's unconditional low-32 update. The source gate keeps the separate
`CNTKCTL_EL1, X3` VHE-sensitive route out of this theorem. It proves no access
admission, dynamic occurrence, X3 provenance, field validity, timer behavior,
ordering, or synchronization.

## Executable refinement test

The AArch64 freestanding test compiles the actual Oak example and requires this ordered assembly pattern:

```text
MSR DAIFSet, #2
MSR HCR_EL2, ...
MSR VTTBR_EL2, ...
MSR VTCR_EL2, ...
MSR CNTHCTL_EL2, ...
MSR CNTVOFF_EL2, ...
MSR SP_EL1, ...
MSR ELR_EL2, ...
MSR SPSR_EL2, ...
ISB
ERET
```

It rejects hidden `DMB`, `DSB`, `WFI`, `WFE`, `SEV`, ordinary `RET`, and heap dependencies.

The direct-native gate additionally reads the actual Oak object symbol and
requires the complete body to be exact DAIFSet, the eight context-register MSR
words, exact ISB word, and exact ERET word, with no stack frame. This executable
regression witness pins the observed static source-to-object bytes and order
for the native lane; it is not a kernel-checked dynamic compiler/execution
trace or an architectural synchronization proof.

## Next milestone

The next correctness increment is live stage-2 maintenance.
`Oak.AArch64Stage2Maintenance` now proves a conditional per-old-event
BBM-shaped local ordering skeleton corresponding to CAT around an abstract
TLBI occurrence. Its concrete wrapper preserves an externally supplied exact
VMALLS12E1IS word/action witness for the same event through that projection;
the word does not create the trace action. Before a previously active guest
context can change translation state, Oak still needs a kernel-checked dynamic
compiler/execution trace supplying that premise and proofs of architectural
target/scope, descriptor publication, invalidation completion, and final
context synchronization. Oak now has an exact zero-overhead source/object leaf
for the fixed `DSB ISH; VMALLS12E1IS; DSB ISH; ISB` slice, but its formal
completed wrapper still requires those execution-level completion and sync
facts explicitly. It is not a descriptor BBM protocol. The current OS
guest-entry and revoke paths use plain `VMALLS12E1`, not the IS operation, and
revoke omits ISB, so this theorem and leaf do not refine them. After those
obligations and the consumer-specific instruction choice are resolved, this
entry path can become the final transfer step of a reusable vCPU re-entry path
and can be exercised in the OS QEMU EL2 smoke test.
