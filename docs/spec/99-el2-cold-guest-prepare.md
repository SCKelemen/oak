# 99 - Cold EL2 Guest Preparation

Status: normative bootstrap protocol for a vCPU that has not yet executed.

## 1. Purpose

This protocol is the first whole hypervisor-shaped Oak program built from the machine primitives in specs 96-98. It installs the initial EL2/EL1 guest execution context before the vCPU has entered EL1.

The reference implementation is `examples/hypervisor/el2_cold_prepare.oak`.

## 2. Preconditions

The protocol is valid only for cold initialization of a vCPU whose stage-2 translation context has not previously been active.

In particular, it does **not** authorize changing VTTBR_EL2 or VTCR_EL2 underneath a live or previously active translation context without the required invalidation/completion protocol. Live stage-2 reconfiguration requires explicit TLBI and DSB machinery that is outside this specification.

## 3. Ordered machine sequence

The reference sequence is:

1. mask IRQ delivery with `arm64.daifset_irq()`;
2. write `HCR_EL2`;
3. write `VTTBR_EL2`;
4. write `VTCR_EL2`;
5. write `CNTHCTL_EL2`;
6. write `CNTVOFF_EL2`;
7. write guest `SP_EL1`;
8. write `ELR_EL2` (guest PC);
9. write `SPSR_EL2` (guest PSTATE restore state);
10. issue explicit `arm64.isb()`.

The final transfer with `ERET` is intentionally absent until Oak can represent a non-returning machine control transfer faithfully as `never`.

## 4. Invariants

- IRQs remain masked throughout preparation.
- Every machine register is selected statically by source identity; there is no runtime register dispatch.
- No heap allocation is introduced by the protocol or its machine helpers.
- No DMB or DSB is silently inserted. This protocol is cold initialization, not live translation reconfiguration.
- No wait/event operation occurs during preparation.
- The ISB is explicit and visible in source.
- This function returns to its EL2 caller; it does not enter the guest.

## 5. Verification

`codegen/aarch64_el2_cold_prepare_test.go` cross-compiles the reference Oak source for freestanding ARMv8-A and checks the emitted assembly for the complete ordered instruction sequence. The test also rejects hidden DMB, DSB, WFI, WFE, or SEV instructions and heap dependencies.

The constituent authority/order facts remain covered by the Lean models for AArch64 system registers, barriers, MMIO, and event control. A later guest-entry state-machine model should compose these facts with `ERET`, stage-2 invalidation, and vCPU lifecycle state.

## 6. Next protocol layers

1. correct bottom-type (`never`) control-flow composition;
2. `ERET` as a non-returning AArch64 control transfer;
3. cold prepare + ERET guest entry;
4. TLBI/DSB primitives and live stage-2 reconfiguration protocol;
5. virtual interrupt/timer entry/exit integration;
6. QEMU EL2 smoke test driven by generated Oak code.
