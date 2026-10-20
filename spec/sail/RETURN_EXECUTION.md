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
TCR_EL1 is zero, and the concrete current-mode/EL-mode configuration profiles
below are initialized. The original `ReturnComposition.exact_bytes_return` theorem retains its explicit
`versions.v85 = false` profile. The new `ReturnBTIExecution.exact_bytes_return`
proves the enabled path described below. `install`
installs the concrete generated current-mode, PAC and BTI feature queries.
Eager queries in the exported model remain present; these premises cover them.
Sign extension, host/EL2 configuration and nonzero-tag paths are not discharged.
The remaining query cuts are explicit.

The intact pinned `HaveEL` and `S1TranslationRegime__0` bodies are now exported
with the same guarded profile. `haveEL_el1` and `regime_el1` prove their actions
equal `pure true` and `pure EL1` for every state and every remaining callback,
without configuration initialization or callback-success premises. Their source
signature/body hashes are checked in `query_bodies` in the manifest. The
configuration registers used by their other branches are represented explicitly;
`haveEL_el2_missing` and `regime_el0_missing` retain `Unreachable` and the complete
unchanged state when the required register is absent. EL0 retains a `get_SCR`
cut and is not covered by the successful-return profile. These checks establish
the generated-model paths, not general original-source/export equivalence.

The PAC query is now the intact pinned `HavePACExt`/`HasArchVersion` export,
with `ArchVersion` and all five `__v81_implemented` through `__v85_implemented`
configuration registers (pinned `aarch_mem.sail` lines 361–369, 1901–1905,
1973–1977; `aarch_types.sail` line 312). `ReturnConfig.Initialized` gives explicit register
values, not callback-success assumptions. `havePAC_run` proves successful,
state-preserving execution returning the v8.3 value. The generated expression
reads all five registers eagerly, including versions irrelevant to the result;
these reads are not erased. A missing v8.1 register fails with `Unreachable`
and preserves the state. `ret_missing_version` additionally proves the installed
RET decoder retains its preceding `__unconditional = true` write on this failure.
Constructive `withValues` witnesses support both the
pinned default `true` and a configured `false`, preserving prior bank/PSTATE/TCR
observations. They do not prove hardware reset, startup or EL1 reachability.

Both PAC values produce the same bounded plain-RET result when TCR_EL1 is zero.
The scalar RET query and both eager AddrTop calls execute the concrete body;
configuration preservation is proved through the actual logical/RET/PC writes.
The former `QueryProfile` callback-success assumptions are now discharged by
concrete mode/configuration reads.
The old scalar observation still uses an explicit projected callback profile;
its PAC value is immaterial on this exact non-authenticating RET path.

`UsingAArch32` is also the intact pinned export, with `HaveAnyAArch32` and
`HighestELUsingAArch32` (pinned `aarch_mem.sail` lines 848–852, 1895–1899,
3882–3894). `ReturnMode.Ready` explicitly requires all four CFG_EL0..EL3
register values, PSTATE with nRW=0, and `__highest_el_aarch32=false`.
`using_run` proves the concrete action returns false with the complete state
unchanged. Actual scalar logical/RET and return-PC writes preserve these facts.
No globally equal-to-pure current-mode callback premise remains.

The source configuration defaults for these four registers are 0x2. The
constructive `withValues` witness accepts arbitrary configuration values and
sets the two current-mode facts explicitly, preserving the bank, TCR, PAC
version profile and memory. This is a nonvacuity witness, not a proof of reset,
boot or EL1 reachability. All four CFG reads occur eagerly. Separate negative
controls preserve missing-register failures for PSTATE, every CFG register,
and the highest-mode register, and retain both inconsistent-configuration
assertion failures. `postdecode_missing_pstate` shows that BTI=false still
permits the exported eager mode read to fail. The EL-specific mode query is justified separately below; current mode and
EL-specific mode are not identified by assumption.

The intact EL-mode caller chain now includes `ELUsingAArch32`,
`ELStateUsingAArch32`, `ELStateUsingAArch32K`, `HaveAArch32EL`, `HighestEL`,
`IsSecureBelowEL3`, `aget_SCR_GEN`, `HaveSecureEL2Ext` and `HaveVirtHostExt`.
Their original signatures/bodies remain pinned in `query_bodies`; the guarded
exporter/profile is unchanged. `ReturnELMode.Ready` explicitly maps CFG_EL0..EL3
to their default value 0x2, requires highest-EL-AArch32=false, and supplies
SCR_EL3/HCR_EL2 with their RW bits (10/31) set. SCR/HCR's other bits and all
architecture-version values remain arbitrary. `el1_run` returns false and the
complete unchanged state for every remaining callback interpretation.

`get_SCR` remains an explicit cut because its original shadowing body is outside
the guarded profile. It is not exported, rewritten or assumed successful:
EL3 is present, so `IsSecureBelowEL3` reads `SCR_GEN`; highest-EL-AArch32=false
selects the direct SCR_EL3 read. The secure-only IMPDEF callback is also outside
this path. `callbacks_irrelevant` and `hostile_callbacks` quantify over arbitrary
callbacks, including failures that would replace the entire state. They prove
result/state independence in this sequential model, not a new hardware event
trace semantics or source/export equivalence for those omitted bodies.

Constructive initialization witnesses preserve the prior register bank, PSTATE,
TCR, PAC profile, current-mode profile and memory. The selected actual scalar
and return writes preserve the EL-mode profile. `each_missing_read_fails`
removes each of the twelve required registers in turn and proves exact
Unreachable failure with unchanged state. Alternate-branch theorems expose the
get_SCR and secure-only IMPDEF callback results outside the profile. Clearing
SCR.RW, or clearing HCR.RW in the shown nonsecure configuration, instead yields
AArch32=true. These controls retain branch/failure behavior; they do not prove
boot/reset reachability, all EL configurations or execution of omitted bodies.

`HaveBTIExt` is the intact pinned wrapper around `HasArchVersion(ARMv8p5)`
(`aarch_mem.sail` lines 2039–2043), using the same five initialized version
registers already in the profile. `haveBTI_run` proves the actual returned v8.5
value and complete state preservation. All five eager reads remain; erasing
each version register gives exact Unreachable failure. Constructive witnesses
show both the pinned default true and explicitly configured false.

The older composition uses concrete reads plus the explicit
`versions.v85=false` condition. Its `postdecode_enabled_boundary` theorem is
retained as a factorization of the enabled control callback.

## Concrete BTI-enabled execution

`ReturnBTIExecution.exact_bytes_return` covers the same exact three logical
words and plain RET with `versions.v85=true`, including the pinned default
version values. It installs the actual guarded export of `BranchTargetCheck`;
there is no successful or state-preserving callback premise for that check.
The added intact helpers are `ThisInstr`, `ThisInstrAddr`, `Halted`,
`AArch64_ExecutingBTIInstr`, and `AArch64_ExecutingBROrBLROrRetInstr`.
Their signatures/bodies are pinned separately in `query_bodies`. The guarded
compiler, patch and admission policy are unchanged. The scalar raw export is
still the original official artifact.

The initialized control profile requires PSTATE.BTYPE=00, EDSCR=1 (ordinary
running state), and explicit values for InGuardedPage and BTypeCompatible.
Both Boolean values are accepted for each of the latter registers. Even with
BTYPE=00, the exported Boolean expression eagerly reads compatibility and debug
state. Those reads are retained. The architectural-version and AArch64-mode
queries also retain all their prior eager reads. This proves a configured
instruction-entry profile, not complete default machine state or reset/startup
reachability.

For AND/ORR/EOR, the actual check writes BTypeNext=00 before the logical body.
For RET, PostDecode preserves BTypeNext, then the existing RET body writes00.
The full-state equations keep this sequencing. The new current-instruction,
compatibility and debug registers are explicitly represented. The total
projection back to the original scalar state preserves all its registers and
non-register fields; `final_state_frame` shows that the new final state differs
from the existing return result only by the explicit current-instruction value.

Each harness dispatch first writes its decoded word to __currentInstr, then
uses the existing SEE=-1 initializer and selected scalar dispatch. The same
word comes from `takeWord(functionBytes op)`; the production compiler/ELF pin
checks all three actual byte sequences against this theorem. Pinned
`main.sail` at the same Arm revision writes the fetched A64 word to
__currentInstr (line94) and calls decode64 on that register (line140).
`--check-source` also pins that complete file, SHA256
`9831f30fe70bd10bb65dd9055b1dc29da3c3c1789d257b8a1788cc75d11c9cb9`.
The small harness is an explicit prefetched-word adapter, not an export of
main, proof of fetch, or proof of intermediate PC advancement.

`ReturnBTIControls.initial_admits` constructs the complete enabled profile for
arbitrary operand banks and both guarded-page values, with the existing EL1
return configuration. Missing version, PSTATE, guarded-page, compatibility,
debug or current-instruction reads preserve the exact failure state.
`logical_dispatch_missing_version` retains the current-word, SEE and
unconditional writes preceding the failed query.

The exception callback remains arbitrary. BTYPE=00 proves it unreachable even
if it would fail and replace the entire state. Outside that profile, the
nonzero-BTYPE, guarded, incompatible, non-halted branch retains the actual
exception call: failure propagates its exact error/state; successful state
changes feed the subsequent instruction recognizers and BTypeNext update.
Exception delivery itself is not proved. Neither are BTI hints, arbitrary
branch instructions, authentication, or all possible BTYPE values successful.

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
  default target. `ReturnBTIControls` is also a default target and imports the
  enabled execution/projection graph. `audit_return.py` fail-closes on missing/extra results or any
  axiom outside the standard allowlist, and runs in that same CI lane. Reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `TestArmBTIEnabledCompilerBytes` binds actual compiled AND/OR/XOR function
  bytes to the all-input enabled theorem and rejects changed byte artifacts.
  The formal Sail lane requires it.
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

The focused enabled-proof validation used Lean 4.33.1 with the same pinned Sail
support cache as the earlier return graph. A bare `import Sail` measured
1,583,180 KiB peak RSS; expanded raw definitions measured 1,628,432 KiB. Local
checks therefore used one child at a time with a 2.5 GiB/60-second ceiling and
a 2 GiB available-memory floor. The largest observed proof module used
1,729,100 KiB. This is resource accounting, not a changed proof option or
permission to exceed unrelated certificate-batch limits. The final local
source/object-bound graph contains 43 modules and 141 standard-only closures;
fresh exact-head hosted generation, build, audit and compiler pins remain
required before merge.
