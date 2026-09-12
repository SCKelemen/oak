# AArch64 system-register operations

This chapter specifies Oak's initial system-register surface for the EL2/EL1
bootstrap path. Register identity is compile-time source identity: callers do
not pass a register number, string, enum, or descriptor at runtime.

The governing rule is:

> Machine control must stay explicit enough that the source shows both the
> register being changed and every required synchronization operation.

## 1. Source surface

Readable registers expose a nullary function:

```text
arm64.read_hcr_el2() -> u64
arm64.read_esr_el2() -> u64
```

Writable registers additionally expose:

```text
arm64.write_hcr_el2(value: u64) -> ()
```

The v1 catalog is deliberately small and OS-driven.

Read-only:

- `CurrentEL`;
- `ESR_EL2`;
- `FAR_EL2`;
- `HPFAR_EL2`;
- `CNTVCT_EL0`.

Read/write:

- `HCR_EL2`, `VTTBR_EL2`, `VTCR_EL2`;
- `CNTHCTL_EL2`, `CNTVOFF_EL2`;
- `ELR_EL2`, `SPSR_EL2`;
- `CNTV_CTL_EL0`, `CNTV_CVAL_EL0`;
- `SP_EL1`, `SCTLR_EL1`, `TTBR0_EL1`, `TCR_EL1`, `VBAR_EL1`;
- `MAIR_EL1`, `SP_EL0`, `ELR_EL1`, `SPSR_EL1` — the kernel adapter's MMU
  register program and EL0 entry (`write_sp_el0`, `write_elr_el1`,
  `write_spsr_el1`, then `eret`).

The library catalog here and the assembler's encoding table
(`asm/sysregs_gen.go`, every register MRS/MSR can name; `94-assembler.md`)
are two surfaces: an `.oakasm` unit may name any encoded register, while
`arm64.read_X`/`arm64.write_X` in Oak source exist only for the registers
listed above.

Adding a register is a language change. Its architectural access direction,
privilege assumptions, source spelling, effect, and backend spelling must be
reviewed together.

## 2. Effects

Reads project to:

```text
Machine.SysRegRead[register]
```

Writes project to:

```text
Machine.SysRegWrite[register]
```

These operations are machine effects. They are not pure integer functions even
when a read returns a `u64`.

## 3. Runtime and allocation contract

Register identity is encoded in the source member name and Semantic-IR catalog.
Generated code contains no:

- heap allocation;
- register enum/string argument;
- runtime register lookup;
- virtual dispatch or callback;
- generic system-register wrapper.

The compiler semantic lookup is bounded and regression-tested at zero
allocations. The C bootstrap backend emits a pay-for-use static-inline helper
containing the exact `MRS` or `MSR` operation.

## 4. Ordering and context synchronization

A system-register read/write does **not** implicitly emit `DMB`, `DSB`, or
`ISB`.

This is essential because AArch64 architectural requirements differ by register
and by transition. For example, control-register changes often require an
explicit context-synchronization sequence, while adding an `ISB` to every
system-register write would be both semantically misleading and expensive.

Required sequences therefore stay visible:

```text
arm64.write_hcr_el2(value)
arm64.isb()
```

when the architecture/protocol requires that sequence.

The bootstrap C inline assembly uses `volatile` plus a compiler `memory`
clobber so the C compiler does not move ordinary memory operations across the
machine-state effect. This compiler-ordering constraint is **not** an AArch64
hardware memory barrier and does not satisfy an architectural `DMB`, `DSB`, or
`ISB` requirement.

## 5. Backend refinement

On AArch64, a read lowers to the semantic equivalent of:

```asm
mrs xN, HCR_EL2
```

and a write to:

```asm
msr HCR_EL2, xN
```

The generated helper fails compilation on non-AArch64 targets. The host
interpreter also fails explicitly rather than manufacturing synthetic system
state.

Freestanding cross-compilation tests inspect optimized AArch64 assembly and
require the exact `MRS`/`MSR` register name while rejecting hidden `DMB`, `DSB`,
or `ISB` instructions in that operation's function body.

## 6. Formal verification

`spec/lean/Oak/AArch64SysReg.lean` mirrors the exact v1 register set and proves:

- all catalog registers are readable;
- `CurrentEL`, `ESR_EL2`, `FAR_EL2`, `HPFAR_EL2`, and `CNTVCT_EL0` are not
  writable through the language surface;
- any legal write is to a register classified writable;
- system-register operations themselves provide no memory-ordering,
  completion, or instruction-synchronization capability.

These are language/catalog properties. They are not a proof that an arbitrary
sequence of register writes satisfies the Arm Architecture Reference Manual.
Protocol-specific ordering obligations remain separate specifications and tests.

## 7. Verification status

| Layer | Status |
| --- | --- |
| exact register catalog | implemented + tested |
| read/write authority | implemented + Lean-modeled |
| zero-allocation semantic lookup | tested |
| source type signatures | implemented + tested |
| host evaluator | fail-closed + tested |
| C bootstrap lowering | implemented |
| exact `MRS`/`MSR` register selection | AArch64 assembly-refinement tested |
| hidden hardware barriers | absence assembly-tested + Lean capability theorem |
| runtime allocation/dispatch | absent by construction |
| protocol-specific register sequencing | not globally proved |
| full Arm axiomatic system-register refinement | not proved |

## 8. Next work

This catalog is sufficient to start expressing the existing hypervisor's pure
EL2 control path in Oak. The next pieces should be:

1. structured unsafe/assumption tracking around privileged machine setup;
2. explicit exception-entry/return and special-instruction contracts (`ERET`,
   interrupt masking, wait/event primitives) rather than treating them as
   ordinary calls;
3. device-memory mapping/MAIR semantics for MMIO;
4. compile a small Oak EL2 register/timer adapter and link it into the existing
   Zig/QEMU OS harness.
