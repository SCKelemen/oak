# Pinned scalar logical and ordinary-RET export

This slice invokes the pinned Sail compiler on **copied original Arm bodies**,
not a new hand-written implementation of their intended arithmetic. It proves
a stateful register result and a precisely exposed return-call boundary.

## Reproduce

Use Lean 4.33.1 and `spec/sail/setup.sh`'s patched lean-sail revision
79b4d08505af29d88b3918f32d29840fae1fa191. Source files are from official
rems-project/sail-arm commit 1bf2e5574ba9d704639a28401b6a387dcb113cae,
under `external/sail-arm/arm-v8.5-a/model`. The generator checks the full SHA256
of all five input files, not merely snippets.

Use the official Sail 0.20.2 binary release, generator revision
3b7af38d66466ecadad563158b07ce2f82fe05da. Linux x86_64 archive SHA256:
26b59bcab2d66e9f220d317dfe45f8b09170ed70e59a824553d6f525134d1ff6.
These are the existing ARM pins in formal-sail.yml; they differ from the RV64
development exporter. Prepend the release's `sail/bin` directory to PATH,
including its bundled z3. No local opam sandbox change is needed.

Commands from the repository root:

    python3 spec/sail/scalar_execution_regen.py
    (cd spec/sail/lean && lake build ScalarExecutionBridge)
    OAK_REQUIRE_ORACLES=1 go test ./asm -run '^TestSailScalarExecution' -count=1 -v

`--output-dir DIR` generates a
separate comparison tree without modifying checked-in files. Required local
regeneration and Lean tests pass without skips. The future CI addition should
run that same required oracle regex; no new artifact workflow is necessary.

Raw generated Lean is retained as Raw.lean and RawDefs.lean. Their hashes are
pinned in the generator and Go regression test. Generated.lean/Defs.lean add
only a namespace and explicit callback parameters/imports; **no generated
function body or Boolean expression is normalized or replaced**. Interface.lean
defines arbitrary, potentially failing/effectful cut callees, with no successful
default instance. Raw export SHA256:
db0b8ed93db97925f152d508f3c2020230c13c09cf5ea29942a4666d3df24f83.
Raw definitions SHA256:
4599759ae12f5aff5af70c4fcc35fb4fff1d56bbfa6ef94c8997426fedaeac01.

## What is copied and proved

The extracted source includes original register bank declarations, ProcState,
aget_X/aset_X, ZeroExtend__0, LSL, ShiftReg, scalar logical body/field decoder,
__PostDecode, ordinary register-branch body/field decoder, and the four original
decode64 clauses selected by the exact words. The original LSL_C has a modern
Sail typechecking incompatibility at its carry-bit index; it remains an explicit
arbitrary cut. The original LSL zero arm is copied and proved never to invoke
that cut. Non-LSL shifts are also cuts not reached by the selected theorem.
Prelude compatibility adapters are the same width/unsigned/zero constructors
used by the existing extraction; the modern vector prelude is pinned, with only
its unused signed declaration renamed to avoid an old-source identifier clash.

`logical_body_run` proves actual generated scalar execution succeeds for every
initialized 31-register bank and writes only X0 with the zero-extended 32-bit
AND/OR/XOR result. It does not use vector logical-instruction analogies.
`result_eq_common` proves exact correspondence with Oak.BitwiseFunction.eval.
`logical_fields_run` retains the original __unconditional and PostDecode prefix.

`ret_body_factorization` proves that original generated RET reads X30, writes
BTypeNext=00, and calls the explicit BranchTo boundary with BranchType_RET.
`function_bytes_to_return_request` composes the exact eight emitted little-endian
bytes through the selected original clauses and these bodies, retaining the
complete BranchTo result, including its errors and post-state.

Request-state theorems prove the computed bank, zero-extended result, BTypeNext,
and preservation of PSTATE and the sequential memory/tag fields. These are
fields of this generated fragment's state. No equality to the older Out state
or to the complete architectural state is assumed.

## Export behavior and explicit configuration obligations

Sail 0.20.2's Lean exporter eagerly lifts nested Boolean actions. The retained
raw export therefore queries UsingAArch32 even when HaveBTIExt returns false,
and queries HavePACExt even on the non-PAC RET route. The no-BTI/AArch64 theorem
profile requires the first two callbacks to return false successfully without
changing state. The non-PAC theorem permits either PAC-feature value but requires
that extra query to succeed without changing state. The two eager-failure
regressions prove that these callbacks' failures/post-states cannot be ignored.

This is an exact theorem about the **unchanged exported semantics**, conditional
on those extra obligations. It is not a general proof that the exporter preserves
original short-circuit Sail/ASL behavior. Relating these callback results to an
actual complete Arm configuration remains an external obligation. No BTI check,
PAC authentication or control-protection check is silently implemented as success.

## Boundaries still open

- The four copied clauses plus rejecting fallback are a **selected decoder**.
  The extraction finds a unique matching parsed bit-pattern header for each
  selected word, but this is finite source evidence, not a Lean proof of the
  complete decoder's preceding-clause/guard/first-match behavior. Full dispatch
  refinement remains open. Other valid instructions are deliberately absent.
- The adapter explicitly resets SEE before each word. It does not prove that an
  architectural fetch/decode loop supplies this initialization.
- `ReturnBoundary` requires aligned X30, successful real BranchTo behavior, and
  register-bank framing. Alignment alone does not discharge address mapping,
  canonicality/tag treatment, control protection, exception routing or execution
  configuration. These obligations must be instantiated via a full-state relation.
- `successful_function_under_return_boundary` establishes success only under the
  named control and return premises. It never equates a pc-only update with full
  BranchTo semantics or claims hardware fetch/loader/OS correctness.
- Oak source parsing/lowering and actual Go implementation refinement are outside
  this module. The shared native-byte and source-profile modules are prerequisites,
  not replaced definitions. No production verified label or verdict is enabled.

The standard Sail trivial choice source is used. Initial undefined temporaries
are overwritten on the selected path; their generated choice-state handling is
proved explicitly rather than asserted as an axiom. Public theorem audits use
only propext, Classical.choice and Quot.sound, with no sorryAx/native-decide axiom.
