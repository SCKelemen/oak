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

## 6. Next protocol layers

1. refine concrete TLBI/DSB primitives and architectural completion into the
   conditional stage-2 maintenance skeleton;
2. discharge `ArmContextSync` against an occurrence-indexed Arm execution
   model;
3. typed register/configuration builders for HCR/VTCR/SPSR values;
4. virtual interrupt/timer entry/exit integration;
5. QEMU EL2 smoke tests driven by generated Oak code.
