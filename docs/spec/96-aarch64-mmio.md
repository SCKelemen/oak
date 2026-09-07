# AArch64 typed MMIO

This chapter specifies Oak's first executable memory-mapped I/O surface. It is
an architecture-specific bootstrap surface under `arm64`; a future extensible
machine-library mechanism may lift the same nominal register types into a
portable `mmio` namespace without changing their semantics.

The governing rules are:

> A register address is typed authority, not an integer convention.

> One MMIO source access means exactly one volatile-width machine access and no
> hidden barrier.

## 1. Register identity

A typed register handle has two static dimensions:

- width: `u8`, `u16`, `u32`, or `u64`;
- access authority: read-only, write-only, or read-write.

The typechecker represents these as nominal
`arm64.MMIO[carrier,access]` types. Different widths and authorities do not
implicitly convert.

The current source surface keeps register handles expression-local because Oak
has not yet exposed these compiler-owned nominal machine types in type position.
They are nevertheless real checked types: constructor results can only flow to
operations accepting the exact same width/authority. Exposing annotations such
as `mmio.Reg[u32,ReadWrite]` is a later surface-language refinement, not a
change to the machine semantics.

## 2. Assumption-bearing construction

Construction is deliberately named `unsafe`:

```text
arm64.mmio_unsafe_ro_u32(address: u64)
arm64.mmio_unsafe_wo_u32(address: u64)
arm64.mmio_unsafe_rw_u32(address: u64)
```

with the same three constructors for `u8`, `u16`, and `u64`.

Construction asserts facts Oak cannot derive from address bits alone:

- the address refers to the intended device register;
- the current translation regime maps it with suitable device-memory
  attributes;
- the caller has authority to access that device;
- the register's hardware semantics match its declared access direction.

Oak does check the machine fact it can enforce locally: the address is naturally
aligned to the declared access width. Misaligned construction traps before an
MMIO access is issued.

The current `unsafe_` spelling records the assumption at the operation itself.
A later language revision should require these constructors to occur inside the
same structured `unsafe` assumption blocks used elsewhere, once the typechecker
tracks unsafe context for compiler-known machine calls.

## 3. Read/write surface

For each readable handle:

```text
arm64.mmio_read_ro_u32(reg) -> u32
arm64.mmio_read_rw_u32(reg) -> u32
```

For each writable handle:

```text
arm64.mmio_write_wo_u32(reg, value) -> ()
arm64.mmio_write_rw_u32(reg, value) -> ()
```

and equivalently for `u8`, `u16`, and `u64`.

There is intentionally no read operation for write-only handles and no write
operation for read-only handles. The source catalog contains no such members,
and the typechecker rejects attempts to substitute a handle of the wrong width
or authority.

## 4. Effects

Construction projects to:

```text
Machine.AssumeMmioRegister[carrier, access]
```

Reads and writes project to:

```text
Memory.MMIORead[carrier]
Memory.MMIOWrite[carrier]
```

None of these effects implies allocation, blocking, a syscall, scheduler
interaction, an atomic synchronization edge, or a barrier.

## 5. Runtime representation and allocation

A checked MMIO register handle erases to exactly the `u64` address bits. Width
and access authority are compile-time facts and consume no runtime tag,
wrapper, heap object, vtable, callback, or dispatch branch.

The compiler-side semantic lookup is regression-tested at zero allocations.
The generated runtime path contains no Oak allocation. Constructor alignment
checking is a bounded integer mask/test; a read/write then lowers directly to
one volatile access of the declared carrier width.

## 6. AArch64 bootstrap backend

The C bootstrap backend lowers a read to the semantic equivalent of:

```c
*(volatile u32 *)(uintptr_t)address
```

and a write to:

```c
*(volatile u32 *)(uintptr_t)address = value
```

using the exact declared width.

The generated helper fails compilation off AArch64. The host evaluator also
fails explicitly rather than dereferencing host process memory or simulating a
device register.

Freestanding cross-compilation tests inspect optimized AArch64 assembly and
require the corresponding access-width instruction (`LDRB/LDRH/LDR` and
`STRB/STRH/STR`). The same function body is checked to contain no hidden
`DMB`, `DSB`, or `ISB`.

## 7. Volatile is not memory type

The volatile source operation guarantees an observable access of the requested
width. It does **not** configure the translation regime.

Correct physical MMIO on AArch64 additionally depends on page-table attributes,
MAIR configuration, shareability, device type (for example Device-nGnRnE vs
other Device forms), and platform-specific interconnect/device requirements.
Those are OS/hypervisor mapping facts and must be established independently.
Oak must not claim that a C volatile pointer magically creates Device memory.

## 8. Barriers are explicit composition

No MMIO operation inserts an architecture barrier. Ordering/completion is
composed explicitly using the barrier surface from `95-aarch64-barriers.md`:

```text
arm64.mmio_write_rw_u32(...)
arm64.dsb_sy()
```

when that is what the device/architecture protocol requires.

This separation is intentional: automatically surrounding every device access
with a full barrier would be both semantically wrong for many protocols and a
major performance regression.

`Oak.AArch64Mmio` proves that the abstract capability of MMIO read/write has no
hidden ordering, completion, or instruction-synchronization capability.

## 9. Formal verification

`spec/lean/Oak/AArch64Mmio.lean` proves:

- write-only authority cannot perform a read;
- read-only authority cannot perform a write;
- read-write authority admits both operations;
- every legal read/write carries the corresponding static authority;
- `u32` construction means alignment modulo 4;
- `u64` construction means alignment modulo 8;
- MMIO access itself provides no memory-ordering, completion, or instruction
  synchronization capability.

These are language/source-surface facts. They do not constitute a formal model
of the full Arm memory system, page-table attributes, or a specific device.

## 10. Verification status

| Layer | Status |
| --- | --- |
| width/access semantic catalog | implemented + tested |
| nominal width/access type identity | implemented + tested |
| forbidden RO/WO operations | absent from source catalog + tested |
| natural alignment predicate | implemented + tested |
| access/alignment laws | proved in Lean |
| no-hidden-barrier capability | proved in Lean |
| evaluator behavior | fail-closed + tested |
| C bootstrap lowering | implemented |
| generated runtime allocation | none by construction; source checked for heap primitives |
| AArch64 exact access width | assembly-refinement tested |
| hidden barrier absence | assembly-refinement tested |
| actual device-memory attributes | external OS mapping obligation |
| full Arm axiomatic refinement | not proved |
| structured `unsafe {}` enforcement for constructor | pending |
| user-spellable architecture-neutral register type | pending |

## 11. Next work

The next machine layers are:

1. expose the nominal register type in ordinary type position without losing
   the zero-runtime representation;
2. connect unsafe MMIO construction to structured assumption tracking;
3. specify page-table/MAIR device-memory attributes as typed mapping facts;
4. add system-register instruction functions needed to configure EL2/EL1;
5. exercise the resulting surface from the Oak IRQ/timer experiment and the
   existing Zig hypervisor harness.
