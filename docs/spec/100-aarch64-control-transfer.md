# AArch64 control transfer

Status: executable language contract for the first non-returning privileged control transfer.

## Scope

Oak exposes AArch64 exception return as:

```oak
arm64.eret() -> never
```

`ERET` is not an ordinary function return, an event-control operation, or a memory barrier. It consumes architectural exception-return state such as `ELR_EL2` and `SPSR_EL2` and transfers control according to the AArch64 architecture.

The initial surface contains exactly one control transfer: `eret`.

## Type and control-flow contract

The source result type is `never`, Oak's existing bottom type. Oak must not type `ERET` as `()` merely to accommodate a backend ABI: that would falsely permit ordinary continuation after an operation that never returns to its caller.

A function whose final expression is `arm64.eret()` may therefore be declared `-> never` today. The semantic type lattice already specifies and proves `never` as bottom. General expected-position use of `never <: T` is separate checker-integration work; this chapter does not claim that every expression consumer already uses the lattice relation.

## Effects

`ERET` contributes:

```text
Machine.ControlTransfer[eret]
```

It does not itself establish:

- memory ordering;
- memory completion;
- instruction synchronization;
- interrupt-controller acknowledgement;
- a scheduler handoff.

Any required `DMB`, `DSB`, `ISB`, system-register writes, or interrupt masking must remain explicit in the surrounding Oak protocol.

## Backend contract

The AArch64 C bootstrap backend lowers the operation to an inline `ERET` instruction in a `noreturn` helper. Compiler control-flow metadata may mark the path unreachable after that instruction, but it must not emit a runtime return, heap allocation, dispatch table, opcode switch, or hidden barrier.

Non-AArch64 compilation fails closed rather than emulating exception return. The host evaluator likewise fails closed and never fabricates a new exception level or program counter.

## Performance contract

The operation is pay-for-use and allocation-free:

- semantic lookup allocates zero objects;
- register/instruction identity is fixed at compile time;
- there is no runtime opcode or callback dispatch;
- generated machine code contains the architectural control transfer directly.

## Verification

The acceptance surface includes:

1. SemIR tests for the exact one-member catalog and zero-allocation lookup.
2. Typechecker tests that `arm64.eret()` is nullary and has type `never`.
3. Host-evaluator tests that execution fails closed.
4. Freestanding AArch64 assembly tests requiring `ERET` and rejecting an ordinary `RET` path, hidden barriers, wait/event instructions, and heap dependencies.
5. Lean `Oak.AArch64ControlTransfer` proofs that ERET is non-returning, is an exception-context transfer, and supplies no hidden barrier capability.

These facts prove the declared abstraction and test its implementation/refinement boundary. They do not by themselves prove that arbitrary values written to `ELR_EL2`/`SPSR_EL2` form a valid guest context. That obligation belongs to the higher-level EL2 guest-entry protocol.

## Next protocol

The cold guest-preparation sequence in `99-el2-cold-guest-prepare.md` may be extended with this primitive to form an actual cold guest-entry operation:

```text
prepare EL2/EL1 state
    -> explicit ISB
    -> ERET
```

Live stage-2 reconfiguration remains separate and requires the appropriate TLBI/DSB protocol before guest re-entry.
