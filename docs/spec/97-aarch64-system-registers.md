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
  `write_spsr_el1`, then `eret_x0(arg)`; `100-aarch64-control-transfer.md`).

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

The stage-2 root write has an additional exact, conditional seam.
`Oak.AArch64Encoding` computes `MSR VTTBR_EL2, X1` as `0xd51c2101` from
the generated general-MSR and SysReg tables. Generated Lean from the local
Sail projection selects VTTBR_EL2/X1 and proves the successful component body
matches Oak's model. At EL2 it directly replaces the VTTBR_EL2 component with
the supplied 64-bit value. For the official EL1 nested-virtualization
alternative, Lean records a redirect flag and leaves that component unchanged;
it does not model NVMem contents or effects. A source-drift gate separately
audits the assignment to NVMem and pins the route to the official Sail model.

The adjacent stage-2 control write is also exact. Lean computes
`MSR VTCR_EL2, X2` as `0xd51c2142`, selects VTCR_EL2/X2, and proves the direct
EL2 component transition. Unlike VTTBR_EL2, the pinned official model declares
VTCR_EL2 as `bits(32)`: the direct result is exactly X2 bits 31:0, not the full
64-bit argument. The EL1 redirect leaves the projected component unchanged;
the source gate audits the corresponding low-32-bit NVMem(64) assignment.

The timer-control write follows the same width boundary but a different body.
Lean computes `MSR CNTHCTL_EL2, X3` as `0xd51ce103`, selects the exact tuple,
and proves its admitted body unconditionally stores X3 bits 31:0 in the
official 32-bit component. The source gate follows the complete op1=100 route.
It separately counts the model's second CNTHCTL assignment and the generated
decoder rejects `MSR CNTKCTL_EL1, X3`; that VHE-sensitive op1=000 path is not
silently merged into Oak's CNTHCTL theorem.

The counter-offset write is full-width and conditional. Lean computes
`MSR CNTVOFF_EL2, X4` as `0xd51ce064`, selects CNTVOFF_EL2/X4, and proves the
direct EL2 body installs the supplied 64-bit value. The projected EL1 nested-
virtualization alternative preserves old CNTVOFF and raises a redirect flag;
the source gate pins the same old HCR/SCR aliases and the official NVMem(96)
assignment. The proof does not connect those Booleans to architectural state.

The preceding HCR write has the parallel exact seam. Lean computes
`MSR HCR_EL2, X0` as `0xd51c1100`, selects HCR_EL2/X0, and proves the projected
component body directly installs the supplied value at EL2. The redirect
predicate is explicitly a projection of the old HCR_EL2 NV/NV2/TGE bits plus
SCR_EL3 NS/EEL2; it is never derived from the incoming HCR value. Lean records
the EL1 alternative as a redirect flag and unchanged HCR_EL2, while the source
gate separately audits the official NVMem(120) assignment. The proof does not
connect those separately supplied old-bit Booleans to the old 64-bit component.

These are language/catalog properties. They are not a proof that an arbitrary
sequence of register writes satisfies the Arm Architecture Reference Manual.
Protocol-specific ordering obligations remain separate specifications and tests.

The VTTBR theorem does not prove system-access admission, absence of traps,
dynamic execution, or that runtime X1 contains the Oak argument beyond the
existing static ABI/object regression witness. It validates no VMID, BADDR,
CnP, reserved bit, alignment, VTCR compatibility, table initialization,
publication, coherence, BBM, TLBI effect, completion, or context
synchronization property.

The HCR theorem likewise proves no access admission, trap absence, dynamic
execution, runtime X0 argument provenance, field validity, RES0/RES1 or feature
compatibility, desired VM/RW/interrupt-routing configuration, stage-2
enablement, exception routing, or observation by later writes. It supplies no
ordering, synchronization, publication, BBM, or TLBI fact.

The VTCR theorem proves no access admission, trap absence, dynamic execution,
runtime X2 provenance, or preservation of X2 bits 63:32. It validates no VTCR
field, RES0/RES1, feature, granule, or address-size constraint and no VTTBR
compatibility. It proves no stage-2 enablement or walk behavior, publication,
ordering, BBM, TLBI effect/completion, context synchronization, NVMem effect,
or preservation of other machine state.

The CNTHCTL theorem proves no access admission, minimum exception level, trap
absence, dynamic occurrence, or runtime X3 provenance. It validates no field,
RES0/RES1, or feature-dependent constraint and proves no guest timer/counter
permission, event-stream behavior, VHE alias semantics, ordering, completion,
context synchronization, upper-32-bit preservation, or other architectural
state.

The CNTVOFF theorem proves no access/minimum-EL admission, trap absence,
dynamic occurrence, runtime X4 provenance, predicate-state consistency, or
NVMem effect. It proves no offset validity, virtual-counter arithmetic,
wraparound or monotonicity property, guest timer behavior, relation to
CNTHCTL, ordering, completion, context synchronization, or other state.

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
| exact HCR_EL2/X0 word and conditional component update | Lean/Sail proved; official source drift-pinned |
| exact VTTBR_EL2/X1 word and conditional component update | Lean/Sail proved; official source drift-pinned |
| exact VTCR_EL2/X2 word and low-32 conditional component update | Lean/Sail proved; official source drift-pinned |
| exact CNTHCTL_EL2/X3 word and direct low-32 component update | Lean/Sail proved; official source drift-pinned |
| exact CNTVOFF_EL2/X4 word and conditional full-width component update | Lean/Sail proved; official source drift-pinned |
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
