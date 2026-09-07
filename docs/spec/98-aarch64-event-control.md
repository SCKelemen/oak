# 98 - AArch64 Event and Interrupt Control

Status: normative bootstrap machine surface.

## 1. Scope

Oak exposes a deliberately small set of AArch64 event and interrupt-control instructions needed by low-level runtime and hypervisor code:

- `arm64.daifset_irq()` -> `MSR DAIFSet, #2`
- `arm64.daifclr_irq()` -> `MSR DAIFClr, #2`
- `arm64.wfi()` -> `WFI`
- `arm64.wfe()` -> `WFE`
- `arm64.sev()` -> `SEV`

All operations are nullary and return Unit. The instruction choice and any immediate are encoded by the source member itself; there is no runtime opcode, enum, string lookup, callback, or dispatch.

## 2. Authority and semantics

`daifset_irq` masks the IRQ bit in PSTATE. `daifclr_irq` unmasks that bit. These functions intentionally expose IRQ masking only; broader DAIF manipulation is not part of this v1 surface.

`wfi` and `wfe` may suspend forward execution according to AArch64 architectural event/interrupt rules. They are therefore explicit machine effects and must never be introduced by an optimizer as an ordinary power hint.

`sev` sends an architectural event. It does not by itself publish ordinary memory under Oak's language memory model.

## 3. Ordering boundary

None of these operations is an Oak memory barrier.

In particular:

- `WFI`, `WFE`, and `SEV` do not silently add `DMB`, `DSB`, or `ISB`;
- DAIF mask changes do not silently add `ISB`;
- a C compiler `memory` clobber in the bootstrap backend prevents compiler motion across the inline assembly but is not an AArch64 hardware memory barrier.

When a protocol requires ordering, completion, or instruction synchronization, Oak source must spell the corresponding `arm64.dmb_*`, `arm64.dsb_*`, or `arm64.isb()` operation explicitly.

## 4. Representation and cost

These are pay-for-use helper functions in the bootstrap C backend. A used operation lowers to exactly the named architectural instruction, plus ordinary call/inlining mechanics eliminated by optimization. No allocation or runtime dispatch is permitted.

Host/non-AArch64 code generation fails closed. The sequential evaluator also fails closed rather than pretending to suspend, change PSTATE, or send an architectural event.

## 5. Verification obligations

The implementation is guarded by:

1. zero-allocation SemIR lookup tests;
2. typechecker tests for nullary Unit signatures;
3. freestanding AArch64 assembly tests requiring exact `MSR DAIFSet, #2`, `MSR DAIFClr, #2`, `WFI`, `WFE`, and `SEV` instruction shapes;
4. negative assembly checks forbidding hidden `DMB`, `DSB`, or `ISB`;
5. Lean `Oak.AArch64EventControl` facts separating IRQ-mask, wait, event-send, and memory-ordering capabilities.

## 6. Non-goals

This surface does not yet define:

- `ERET` or other non-local control transfer;
- full DAIF read/write or FIQ/SError/debug-mask policy;
- scheduler semantics for sleeping vCPUs;
- proof that a particular wait/wakeup protocol has no lost wakeup;
- interrupt-controller acknowledgement/EOI semantics;
- a full Arm axiomatic model for architectural events.

Those require higher-level protocols rather than being hidden inside these instruction primitives.
