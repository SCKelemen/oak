# Bounded AArch64 return composition

This is a local, experimental external-model composition. It does not promote a
production verified verdict or claim full ASL/Sail-source faithfulness.

## What the kernel checks

`ReturnSimulation.lean` connects the existing exact eight-byte u32 AND/OR/XOR +
RET model to the generated `BranchTo` body. For all register-bank inputs:

- X0 is the zero-extended u32 bitwise result; the other bank entries are framed.
- The selected decoder/RET path records `BTypeNext = 0` and passes initial X30.
- Actual generated `BranchTo` writes `_PC = X30` and `__PC_changed = true`.
- Every other extended-state field is unchanged by that return.
- A total projection preserves all six original scalar registers, including
  every `ProcState` field, absent-register entries, choice state, memory, tags,
  cycle count, and output. The old official scalar execution with an explicitly
  projected return observation commutes with this projection.

The original scalar state has no PC/TCR fields. Its observed return is therefore
an explicit no-op observation, not a premise that architectural return is a
no-op. `ReturnStateProjection.project_final` and the execution simulation prove
that erasing the new fields has precisely this effect.

The supported return configuration is intentionally narrow: PSTATE.EL is EL1,
TCR_EL1 is zero, and the following cut actions must be successful and read-only:
`HaveEL(EL1)=true`, `S1TranslationRegime(EL1)=EL1`,
`ELUsingAArch32(EL1)=false`, `HavePACExt()=false`, and
`UsingAArch32()=false`. The scalar control profile additionally requires
`HaveBTIExt()=false`. `install` shares the mode/PAC actions between components.
Eager queries in the exported model remain present; these premises cover them.
Sign extension, host/EL2 configuration and nonzero-tag paths are not discharged.
No successful implementations of these architectural queries are silently
installed.

The pinned `BranchTo` body itself performs no target-alignment check.
`aligned_return_observation` carries an explicit caller X30 alignment premise.
This is not proof of successful instruction fetch, mapped executable memory,
loader behavior, exception delivery, authentication, or a Linux EL0 run.
`Hint_Branch` is the original pinned body, whose empty behavior is not a claim
about hardware branch prediction. Failed mode queries preserve their complete
error and post-state in `branchTo64_query_failure`.

## Two generator provenances, one proved state relation

The scalar raw bytes remain exactly the official pinned Sail 0.20.2 export,
SHA256 `db0b8ed93db97925f152d508f3c2020230c13c09cf5ea29942a4666d3df24f83`.
Their bodies are not regenerated with the experimental tool. The larger state
uses the copied original type/register declarations; scalar import/namespace
and callback-parameter framing is checked mechanically. The old exact-byte proof
is replayed over that state, and a separate kernel simulation relates it back
to the original state. All six shared registers and all non-register fields are
accounted for, rather than assuming the states are identical.

The return bodies use the separately identified no-shadow profile described in
`repros/guarded_mutation/guarded_profile/README.md`. This profile rejects the
existing complete scalar, STR and primitive fragments because they contain
shadowing. Those rejections remain in force. The return fragment is separately
admitted; no original body is modified to evade the guard.

`AddrTop` has one explicit interface adaptation: its original `int` result
signature is strengthened to the finite set `{31,55,63}`. The original body is
unchanged and Sail checks it against that signature. This is needed because the
isolated original consumer cannot prove its vector-index bounds from plain
`int`. `return_execution_manifest.json` preserves the original/adapted signatures
and body hashes. Regeneration exports the original-signature function separately
and requires its generated body to be byte-identical to the strengthened one.
The kernel independently proves `addrTop_result_range` for every successful
result, with arbitrary callbacks and state. No range/equivalence axiom is added.

## Still outside the theorem

The decoder is the existing four copied clauses, not a proof that the full
first-match decoder selects them. The instruction-byte harness supplies each
word; fetch and intermediate PC advancement are not modeled. Architectural
queries remain explicit cuts. The state is an architectural projection, not all
Arm state. The known official exporter defect remains documented in
`SCALAR_EXECUTION.md`; finite tests plus structural checks do not establish
universal source-to-export equivalence. The guarded profile also does not prove
all earlier/later compiler passes correct.

## Checks

- `go test ./asm -run '^TestSailScalarExecutionReturnFraming$'` always checks raw
  pins, exact framing/proof replay, and byte-mutation rejection without oracles.
  It is included in the existing formal Sail job's mandatory test selection.
- `cd spec/sail/lean && lake build ReturnSimulation` checks the new models,
  concrete execution, total state projection and simulation. It is also a
  default target. `audit_return.py` fail-closes on missing/extra results or any
  axiom outside the standard allowlist, and runs in that same CI lane. Reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `python3 spec/sail/return_execution_regen.py --check-source` verifies intact
  declarations against the pinned external Arm checkout.
- With the exact separate profile available, `--regenerate` checks its executable
  and plugin hashes, regenerates raw output, checks exact bytes, and checks the
  original/strengthened AddrTop body identity. See the profile README for env.

The existing formal Sail lane now performs a fresh source+patch build using the
checksummed official dependency lock, then requires exact raw regeneration and
the guarded regression suite. Its build receipt/logs are retained as CI artifacts.
A local run of that recipe is not a hosted-CI result: adoption must wait for this
lane to pass on the exact proposed commit. The older local binary profile remains
separately identified; receipts from another build do not relabel it.
