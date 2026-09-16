# 99 - Cold EL2 Guest Preparation

Status: normative bootstrap protocol for a vCPU that has not yet executed.

## 1. Purpose

This protocol is the first whole hypervisor-shaped Oak program built from the machine primitives in specs 96-98. It installs the initial EL2/EL1 guest execution context before the vCPU has entered EL1.

The reference implementation is `examples/hypervisor/el2_cold_prepare.oak`.

## 2. Preconditions

The protocol is valid only for cold initialization of a vCPU whose stage-2 translation context has not previously been active.

In particular, it does **not** authorize changing VTTBR_EL2 or VTCR_EL2 underneath a live or previously active translation context without the required invalidation/completion protocol. `Oak.AArch64Stage2Maintenance` now proves a conditional per-old-event BBM-shaped local ordering skeleton corresponding to CAT and can retain an externally supplied exact VMALLS12E1IS word/action witness for its TLBI occurrence. Dynamic trace extraction, architectural target/scope, invalidation/completion, and final context synchronization remain outside this cold protocol.

## 3. Ordered machine sequence

The reference sequence is:

1. execute `arm64.daifset_irq()`; on access-admitted execution its `#2`
   operand sets `PSTATE.I`;
2. write `HCR_EL2`;
3. write `VTTBR_EL2`;
4. write `VTCR_EL2`;
5. write `CNTHCTL_EL2`;
6. write `CNTVOFF_EL2`;
7. write guest `SP_EL1`;
8. write `ELR_EL2` (guest PC);
9. write `SPSR_EL2` (guest PSTATE restore state);
10. issue explicit `arm64.isb()`.

The final transfer with `ERET` is intentionally absent from this returning
preparation helper. The non-returning companion protocol is chapter 101's
`el2_cold_enter`.

## 4. Invariants

- Protocol intent/assumption: maskable IRQ delivery on the executing PE
  remains disabled throughout preparation. The DAIFSet seam proves only the
  access-admitted PSTATE transition, not dynamic occurrence or preservation
  throughout the sequence.
- Every machine register is selected statically by source identity; there is no runtime register dispatch.
- No heap allocation is introduced by the protocol or its machine helpers.
- No DMB or DSB is silently inserted. This protocol is cold initialization, not live translation reconfiguration.
- No wait/event operation occurs during preparation.
- The ISB is explicit and visible in source.
- This function returns to its EL2 caller; it does not enter the guest.

## 5. Verification

`codegen/aarch64_el2_cold_prepare_test.go` cross-compiles the reference Oak source for freestanding ARMv8-A and checks the emitted assembly for the complete ordered instruction sequence. The test also rejects hidden DMB, DSB, WFI, WFE, or SEV instructions and heap dependencies.

`compiler/e2e_native_barrier_words_test.go` separately compiles that same source
through Oak's direct AArch64 backend and requires the complete object-symbol
body to be exact DAIFSet, the eight context-register writes, exact ISB word,
and `RET`. The body has no stack frame or other instruction. This is a
static object-code occurrence/order certificate, not a proof of dynamic
execution or architectural context synchronization.

`Oak.AArch64ColdEntry` now separates the shape-only `ProtocolStep` graph from
an occurrence-indexed `Step`. Its synchronization witness carries all eight
exact register-write occurrences before the same exact ISB word plus an
explicit external Arm context-synchronization proposition. Decoder identity or
Oak's capability bit cannot manufacture that evidence.

The independent DAIFSet theorem computes the first static word, follows the
pinned Sail decoder to the successful DAIFSet body, and proves that body sets
I while preserving D/A/F. `ColdEntry.Step.maskIrq` is not yet connected to a
dynamic occurrence of that instruction.

The HCR seam pins static `MSR HCR_EL2, X0` and proves the generated pure
component body directly writes the supplied value at EL2. Its EL1 redirect is
computed from projected old HCR control bits and SCR bits; Lean erases the
official NVMem(120) effect. This proves no HCR configuration validity, stage-2
enablement, exception routing, later-write observation, access/trap admission,
old-bit-to-old-value consistency, runtime X0 provenance, or dynamic
`ColdEntry.Step` occurrence.

The following VTTBR seam is likewise independent: the native gate pins the
static `MSR VTTBR_EL2, X1` word, while generated Lean follows the general-MSR
projection to the component assignment and proves it writes the supplied value
at EL2. Access/trap admission, runtime X1 value provenance, valid VTTBR fields,
table publication, and a dynamic `ColdEntry.Step` occurrence remain external.

The VTCR seam pins static `MSR VTCR_EL2, X2` word `0xd51c2142` and the official
32-bit register declaration. Generated Lean proves that its direct EL2 body
stores only X2 bits 31:0; the nested EL1 alternative preserves the projected
VTCR component while the source gate audits NVMem(64). It proves no runtime X2
provenance, control-bit consistency with machine state, VTCR field validity,
VTTBR compatibility, stage-2 behavior, ordering, or dynamic occurrence.

The CNTHCTL seam computes `MSR CNTHCTL_EL2, X3` as `0xd51ce103` and proves the
successful official body overwrites the 32-bit component with X3 bits 31:0.
The exact op1=100 route has no redirect; a distinct op1=000 CNTKCTL/VHE route
is explicitly rejected by the local decoder. Access/trap admission, runtime X3
provenance, timer permissions and behavior, ordering, synchronization, and a
dynamic `ColdEntry.Step` occurrence remain external.

The CNTVOFF seam computes `MSR CNTVOFF_EL2, X4` as `0xd51ce064` and proves the
official admitted EL2 body installs all 64 X4 bits. Lean preserves the distinct
EL1 nested-virtualization branch as a redirect flag plus unchanged CNTVOFF;
the source gate audits its NVMem(96) write. Predicate-state consistency,
access/trap admission, runtime X4 provenance, NVMem(96) contents/effects,
offset/counter behavior, ordering, synchronization, and a dynamic occurrence
remain external.

The SP_EL1 seam computes `MSR SP_EL1, X5` as `0xd51c4105` and proves the
official admitted EL2 body installs the complete guest stack value. The EL1
nested-virtualization alternative is a redirect flag plus unchanged SP_EL1;
the source gate audits NVMem(576). Access/traps, predicate-state consistency,
NVMem(576) contents/effects, runtime X5 provenance, stack
validity/mapping/safety, eventual selection after ERET, ordering,
synchronization, and dynamic occurrence remain external.

The ELR_EL2 seam computes `MSR ELR_EL2, X6` as `0xd51c4026` and proves the
official admitted S3_4 body installs the complete 64-bit guest-PC value. It
rejects the distinct ELR_EL1/VHE encoding and does not project that route's
NVMem(560) behavior. Access/traps, runtime guest-PC-to-X6 provenance, address
alignment/canonicality/mapping/executability/PAC, SPSR consistency, ERET
observation or success, ordering, synchronization, other state, and dynamic
occurrence remain external.

The SPSR_EL2 seam computes `MSR SPSR_EL2, X7` as `0xd51c4007` and proves the
official admitted S3_4 body stores exactly guest-PSTATE bits 31:0 in the 32-bit
component. It rejects the distinct SPSR_EL1/VHE/NV route and does not project
NVMem(352). Access/traps, runtime guest-PSTATE-to-X7 provenance, upper-bit
preservation, SPSR mode/DAIF/instruction-state/reserved/feature validity, legal
exception return, relation to ELR_EL2, ERET observation or success, ordering,
synchronization, other state, and dynamic occurrence remain external.

## 6. Next protocol layers

1. refine concrete TLBI/DSB primitives and architectural completion into the
   conditional stage-2 maintenance skeleton;
2. discharge `ArmContextSync` against an occurrence-indexed Arm execution
   model;
3. typed register/configuration builders for HCR/VTCR/SPSR values;
4. virtual interrupt/timer entry/exit integration;
5. QEMU EL2 smoke tests driven by generated Oak code.
