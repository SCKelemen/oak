# A03: shared native target boundary

Inspected baseline: `349fb730` on `specification` (2026-10-20).
Scope: `asm/`, `machine/`, `nativegen/`; existing ARM64/RV64 proofs are retained.

## Contract and ownership

`asm.ResolveNativeTarget` is the shared, closed native lane selector.
Only `arm64` and `rv64` resolve. Empty names, platform spellings (`riscv64`),
aliases, unknown targets, and the zero descriptor cannot select an encoder
or own relocations. `NativeTarget.Encode` also requires an exact function
architecture match and refuses nil input before inspecting instructions.
The descriptor is an opaque value, with no registration or mutable callback API.

`nativegen.CompileFor`, `machine.targetFor`, `asm.EncodeFunction`, object layout,
and `asm.verifierISAFor` consume this selector. Generation and machine passes
retain separate implementation dispatch: registration alone does not implement
a backend. Their default branches still refuse missing implementations.
The dependency direction remains `nativegen → machine → asm`, with
`nativegen → asm`; `asm` must not import either consumer.

Compatibility is explicit: the pre-existing empty-name ARM64 default remains
at `CompileFor`, `machine.targetFor`, `EncodeFunction`, and encoded-object
layout. The strict descriptor and verifier never default. Encoding's wrapper
uses a shallow metadata copy and does not rewrite the caller's function.
A future removal of legacy defaults requires migration of callers and fixtures.
`target.Target` remains the OS/platform and external C toolchain abstraction;
its `AsmArch` conversion is separate from native lane resolution.

Encoding is not proof. A caller must still run seam checking and semantic
verification, and require `VerdictProven` when demanding proof. Unsupported
verification retains the existing non-proven verdict. No ABI table, instruction
semantics, optimization eligibility, proof obligation, or CI gate is relaxed.

## Implementation and evidence map

| Responsibility | ARM64 | RV64 | Required boundary |
| --- | --- | --- | --- |
| Source generation | `nativegen/nativegen.go`, `compileArm64` and OptIR ARM64 lowering | `nativegen/rv64.go`, `compileRV64` and OptIR RV64 lowering | Source/signature/OptIR checks remain mandatory; ISA membership is not eligibility |
| Machine optimization | `machine/target.go`, `arm64Target` | `machine/target.go`, `rv64Target` | Register files, reserved sets, call effects, frame shapes, instruction recognition remain ISA-owned; unknown forms refuse |
| Encoding | `asm/encode.go`, `EncodeInstruction`, generated ISA tables | `asm/rv64_encode.go`, `asm/rv64_rvc.go` | Exact target/function identity; operand validation; CPU feature and compressed-instruction constraints |
| Decoding | `asm/object_relocation.go`, `asm/aarch64_conditional_relocation.go`; selected Lean/Sail instruction models | `asm/rv64_relocation.go`; selected Lean/Sail instruction models | Independent destination decoding for supported relocation patches; no general production decoder interface exists |
| Relocations | `call26`, `jump26`, `branch26`, `condbr19`, `tbz14`, `adr21`, `adrp21`, `lo12`, `adrl21` | `riscv_call_plt`, `riscv_pcrel` | Lane ownership plus format support, full footprint, opcode/register identity, alignment, range, and independent target checks where implemented |
| ABI | `asm/abi.go`, ARM64 checker, generator and machine contracts | `asm/rv64_check.go`, RV64 generator and machine contracts; soft-float and vector options | AAPCS64 versus LP64D/soft-float/RVV distinctions cannot be collapsed to one register list; packed-stack policy remains explicit |
| Verification | `asm/check.go`, `asm/verify.go`, `verifierArm64ISA` | `asm/rv64_check.go`, `asm/rv64_verify.go`, `verifierRV64ISA` | Strict canonical ISA; seam acceptance, symbolic semantics and source equivalence separately required |
| Formal evidence | `Assembler`, `AssemblerSemantics`, `AssemblerCallState`, `ObjectRelocation`, `AArch64AddressRelocation`, AArch64 instruction/bridge models | `AssemblerCallState`, `RV64Relocation`, RiscV instruction/execution models | Existing correspondence tests and Lean/Sail obligations remain; none becomes discharged by shared dispatch |

Object layout now rejects unknown architectures and cross-ISA relocations before
writing a container. Relocation membership does not promise that every object
format or executable writer supports that relocation. Those writers retain their
own refusal paths. Empty object collections retain their existing behavior.

## Validation and limits

Regression tests exercise strict resolution, invalid zero values, nil input,
cross-ISA function identity, actual NOP bytes for each lane, legacy default
non-mutation, all registered relocation ownership pairs, object layout refusal,
and nativegen/machine dispatch. `Oak.NativeTarget` models closed selection and
disjoint relocation ownership. These model properties and finite correspondence
pins are not a universal proof that the Go implementation refines Lean.

Remaining consolidation work:

1. Introduce independently checked decoding capabilities for precisely enumerated
   instruction subsets. Refuse unsupported words; never use encoder round-trip
   equality alone as semantic evidence.
2. Centralize ABI data only after reconciling generator, allocator, seam checker,
   and verifier policies, including ARM64 partial vector preservation and RV64
   soft-float/RVV behavior. Preserve existing conservative approximations.
3. Bind relocation profiles to object/image formats and ISA feature profiles;
   retain each existing patch/decoder theorem and complete end-to-end composition.
4. Separate lowering and machine hook interfaces as additional targets become
   implemented. Adding a name requires lowering, encoding, decoding, relocation,
   ABI, verifier, execution tests, and formal evidence; it cannot enable proof.
5. Full arbitrary source→loaded-image refinement, a complete native decoder,
   and universal Go implementation refinement remain open.
