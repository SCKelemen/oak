# Native encoding target admission

`asm.EncodeFunction` and relocatable object layout share one architecture
admission function. The supported spellings are `arm64` and `rv64`. The empty
string remains an explicit legacy alias for ARM64, matching the existing
`Function` and `EncodedFunction` APIs. New callers should supply a target.
Unknown names are rejected without returning machine code, relocations, or
object bytes. A nil function is also an encoding error.

The public encoder dispatches exhaustively to `encodeARM64Function` or
`encodeRV64Function`. ARM64 instruction encoding and RV64 encoding/relaxation
are unchanged. Object layout validates each function before choosing padding,
relocation handling, and the container machine identifier. ELF remains
available for both native targets; Mach-O remains ARM64-only.

This closes the previous fallback in which an unknown target could produce
ARM64 code and ARM64 ELF/Mach-O metadata. It does not turn Wasm into a native
backend, define a full ABI/feature contract, validate arbitrary supplied
`EncodedFunction.Bytes`, or change proof admission. `EncodeInstruction` remains
the existing ARM64-specific instruction API. Empty objects retain their
existing ARM64 default because that API has no separate target argument.

Regression coverage checks unsupported spellings at both public boundaries,
nil input, exact native return bytes, ELF machine identifiers, and complete
byte equality of legacy and explicit ARM64 ELF/Mach-O objects. Existing
assembler and machine tests cover the unchanged target implementations.
