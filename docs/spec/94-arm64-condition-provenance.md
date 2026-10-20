# ARM64 comparison condition provenance

`Oak.AArch64ConditionProvenance` discharges the Boolean-register assumption
of `Oak.AArch64ControlFlow.checked_successor` for one production slice:
full-width register comparisons emitted by `optIRArm64Selector.compare`,
followed immediately by its register-resident, empty-edge-copy terminator.

The supported source operators are `==`, `!=`, `<`, `<=`, `>`, and `>=` on
`u32`, `i32`, `u64`, and `i64`. The prefix is unshifted register CMP W/X
followed by CSET W. CSET is decoded as CSINC Wd, WZR, WZR using the actual
inverted condition field. Other CMP forms and CSET X are outside this slice.

## Universal model result

The module adds nine theorems, without admitted proofs or added axioms:

- Independent fixed-mask decoders recover every packed CMP operand and
  CSET destination/condition field.
- ArmASL subtraction flags select the mathematical signed or unsigned
  comparison predicate at both widths. The subtraction primitive and
  condition table reuse the existing Sail-connected ArmASL model.
- The inverse condition in CSINC produces exactly zero or one for CSET.
- CMP reads the original operands before CSET updates its destination.
  Reusing either input register as the destination is permitted.
- A W write clears the destination's upper 32 bits and preserves every
  other register. NZCV remains the comparison's flags after CSET.
- `checked_prepare` establishes that the tested register represents the
  comparison for every input register file and initial NZCV state.
- `checked_comparison_successor` composes this prefix with the earlier
  routing certificate and reaches the source comparison's true or false
  successor address, with the exact projected register/flag state.

`checkProducer` requires both actual words to match the selected comparison
and refuses destination register 31: a write to WZR discards the Boolean
and cannot establish its provenance. CMP operands numbered 31 retain the
existing architectural zero-register reading.

## Production evidence

`machine/aarch64_condition_provenance_lean_test.go` invokes the actual
comparison and terminator selector routines and reads their words from
`asm.EncodeFunction`. It checks 504 successful prefix/terminator certificate
pairs: all six operators, four types, three destination placements (separate,
left alias, right alias), and seven layouts covering all five routing shapes
and backward targets. Lean also rejects 1,009 mutations: wrong CMP widths,
missing CSET condition inversion, and a discarded WZR result.

`compiler/aarch64_condition_provenance_lean_test.go` compiles 24 actual Oak
comparison functions. It requires their existing translation-validation
verdicts, an immediate comparison of the two ABI input registers, and words
extracted from the ELF symbols. Each pair receives a Lean theorem for all
register/flag states, including the Boolean-register invariant. These checks
are host independent and do not invoke an external assembler.

The ARM64 proof workflow builds the module and requires both correspondence
tests under `OAK_REQUIRE_ARM64_COND19_LEAN=1`. The existing layout and
source-to-object branch tests continue to run in the same gate.

## Remaining boundary

The universal result is about the projected model. Its correspondence with
the Go compiler remains finite production evidence. It assumes that the
input registers contain the source operands; general value provenance,
narrow-integer normalization, register allocation, spills, intervening
instructions, SSA edge copies, other condition producers, and whole-CFG
simulation remain separate obligations.

Execution is still a no-fault PC/register/NZCV projection with a finite
terminator boundary. Full architectural fetch, faults, memory effects,
PostDecode/BranchTo, and whole-executable/linker correctness are not proved.
