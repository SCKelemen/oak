# AArch64 control transfer

Status: executable language contract for the first non-returning privileged control transfer.

## Scope

Oak exposes AArch64 exception return (`ERET`) as a control transfer with two spellings:

```oak
arm64.eret() -> never
arm64.eret_x0(value: u64) -> never
```

`eret_x0` is the same `ERET` with a **register handoff**: its argument is
in `x0` at the instruction, so the code that runs at the target exception
level receives it as its first argument. ERET itself moves no general
register; the handoff is what is live in the register when the transfer
happens. The kernel adapter's EL0 entry is the motivating shape (the OS
pilot's R6 follow-up):

```oak
el0_enter: (sp: u64, pc: u64, pstate: u64, arg: u64) -> never {
  arm64.write_sp_el0(sp)
  arm64.write_elr_el1(pc)
  arm64.write_spsr_el1(pstate)
  arm64.isb()
  arm64.eret_x0(arg)
}
```

One register is the surface today; a wider handoff (`x0`–`x7`) is a
catalog entry, not a new mechanism (`semir.Arm64ControlTransferSpec.Carries`).

`ERET` is not an ordinary function return, an event-control operation, or a memory barrier. It consumes architectural exception-return state such as `ELR_EL2` and `SPSR_EL2` (or `ELR_EL1` and `SPSR_EL1` from EL1) and transfers control according to the AArch64 architecture.

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

The handoff lowers to a local register variable pinned to `x0` and named
as an input of the `ERET` asm statement: the C compiler places the value
(`mov x0, x1` when it arrived in another register) and emits nothing
else. The refinement test requires that order and forbids any other
instruction between the last system-register write and the `ERET`.

### The assembly-unit form

The same entry is legal as an `.oakasm` unit (`94-assembler.md` §7) under
the `system` capability: bind the parameters, write the registers, move
the argument into `x0`, `isb`, `eret`. The assembler's checker admits
`eret` only from a `never` function and refuses a `ret` path; both forms
produce the same instruction sequence, and a port may choose either — the
Oak-source form is checked by the typechecker and lowered through C, the
unit form is checked instruction by instruction.

```text
el0_enter: (sp: u64, pc: u64, pstate: u64, arg: u64) -> never = {
  system
  bind x0 = sp
  bind x1 = pc
  bind x2 = pstate
  bind x3 = arg
  msr sp_el0, x0
  msr elr_el1, x1
  msr spsr_el1, x2
  mov x0, x3
  isb
  eret
}
```

## Performance contract

The operation is pay-for-use and allocation-free:

- semantic lookup allocates zero objects;
- register/instruction identity is fixed at compile time;
- there is no runtime opcode or callback dispatch;
- generated machine code contains the architectural control transfer directly.

## Verification

The acceptance surface includes:

1. SemIR tests for the exact two-member catalog (`eret`, `eret_x0` carrying `x0`) and zero-allocation lookup.
2. Typechecker tests that `arm64.eret()` is nullary, `arm64.eret_x0` takes one `u64` and no more, and both have type `never`.
3. Host-evaluator tests that execution fails closed.
4. Freestanding AArch64 assembly tests requiring `ERET` and rejecting an ordinary `RET` path, hidden barriers, wait/event instructions, and heap dependencies.
5. Lean `Oak.AArch64ControlTransfer` proofs that ERET is non-returning, is an exception-context transfer, and supplies no hidden barrier capability; that `eret_x0` has exactly ERET's capability (`eret_x0_is_eret`) and carries `x0` alone (`eret_x0_carries_x0`); and that no transfer returns or hides a barrier (`no_transfer_returns_or_hides_barrier`).
6. An end-to-end test that the EL0 entry compiles in both forms — Oak source through `eret_x0`, and an `.oakasm` unit — and that the unit's instruction sequence assembles (`compiler/e2e_el0_entry_test.go`).

These facts prove the declared abstraction and test its implementation/refinement boundary. They do not by themselves prove that arbitrary values written to `ELR_EL2`/`SPSR_EL2` form a valid guest context. That obligation belongs to the higher-level EL2 guest-entry protocol.

## Next protocol

The cold guest-preparation sequence in `99-el2-cold-guest-prepare.md` may be extended with this primitive to form an actual cold guest-entry operation:

```text
prepare EL2/EL1 state
    -> explicit ISB
    -> ERET
```

Live stage-2 reconfiguration remains separate and requires the appropriate TLBI/DSB protocol before guest re-entry.
