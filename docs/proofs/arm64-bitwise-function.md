# ARM64 u32 bitwise leaf-function projection

Supported expression: exactly `op(parameter 0, parameter 1)`, where `op` is
AND, OR or XOR, with two u32 inputs and one u32 result. Shared meaning is
`Oak.BitwiseFunction.eval`.

The complete selected function is `AND/ORR/EOR W0, W0, W1; RET X30`. The
little-endian bytes are decoded independently into the supported logical
register fields and ordinary RET register. The logical decoder fixes sf=0,
N=0, LSL, and shift amount zero, rejects other classes, and observes WZR
read/write behavior. Function invocation rejects truncation and trailing
bytes and cannot conclude success from matching faults.

## Proved in the Lean kernel

- Exact selected function bytes successfully execute for every architectural
  register input in the explicit local no-fault transition model.
- Low X0/X1 halves are the u32 inputs, irrespective of their upper halves.
- W0 is written with the zero-extended u32 result.
- All other registers, SP and NZCV are preserved; projected return PC equals
  the incoming X30.
- Admission binds ARM64, the named AAPCS64 u32 boundary, both parameter
  widths, result width, requested operator, and the complete byte string.
- Any changed byte string is rejected, including otherwise valid different
  operations/registers, truncation and trailing bytes. Separate decoder
  regressions reject unsupported shift/inversion/width/flags and bad RET bits.

`asm/aarch64_bitwise_function_lean_test.go` independently runs the real Go
assembler for all three bodies and binds its emitted bytes to Lean's literals.
It also checks the generated ISA rows, register fields and no-shift defaults.
These tests are finite implementation correspondence evidence, not a universal
proof of the Go assembler or source compiler.

## Explicit remaining external composition

The existing pinned Sail bridge theorem
`Oak.SailBridge.ordinary_ret_x30_generated_decode_exact` establishes static
ordinary RET dispatch and X30 selection only. It does not execute X30 reads,
PostDecode, BranchTo, fetch, alignment, translation, faults or target checks.

The selected pinned Sail fragment currently contains vector logical bodies,
but lacks the **scalar** logical shifted-register decoder and body projection.
A complete external composition must add/source-check that scalar projection,
prove the no-shift W-register read/result/zero-extending write transition,
and compose the ordinary RET dynamic transition under explicit successful
fetch/branch premises. Reusing vector AND/ORR/EOR value equations would not
establish this scalar chain. This module deliberately does not do so.

The model does not establish Oak source parsing/lowering, register allocation,
frame creation, placement/loading, instruction fetch, dynamic external Arm
execution or concrete certificate/graph/CNF/LRAT provenance. Its ABI name
states the modeled boundary, not a universal AAPCS implementation proof.
Production `VerdictProven` and `TranslationVerified` behavior remains unchanged.
