# Pinned Sail guarded-mutation exporter discrepancy

This is a **known-discrepancy regression**, not a successful source-equivalence
check. It prevents an exporter defect from being hidden by a passing proof
about its generated output.

## Reproduced results

With official Sail 0.20.2, revision
3b7af38d66466ecadad563158b07ce2f82fe05da:

- `minimal_total.sail`: Sail's own interpreter returns **55** for
  `repro(false, 1)`; unchanged raw generated Lean returns **63**. The match has
  a default arm and produces no incomplete-match warning. `TotalEvidence.lean`
  proves the exported result by `rfl`, without any axioms, and evaluates it.
- `minimal_incomplete.sail`: the original reduced case is retained. Its source
  interpreter also returns 55 and its unchanged generated Lean returns 63.
  Its stateful `rfl` theorem uses only propext and Quot.sound.
- The original pinned `AddrTop` signature and body are copied unchanged into
  an explicit EL1/AArch64/no-PAC test fixture. With address zero and
  `IsInstr=true`, Sail's interpreter returns **63** for `TCR_EL1=0`, and **55**
  for `TCR_EL1=0x0000002000000000` (TBI0, bit 37, set).
- The raw full AddrTop fixture exhibits the same branch-local shadowing shape,
  but fails Lean 4.33.1 elaboration at an unused `tbid` binding. **No executable
  raw AddrTop result is claimed.** Its raw export and failed build log are
  preserved, without adding type annotations or editing its body to make it run.

The total reproducer distinguishes the original outer mutable `value` from
the shadowing `let value` emitted inside each guarded arm. The generated final
condition still reads the original value. Source-interpreter execution, not
manual source interpretation alone, establishes the discrepant source result.

`evidence/manifest.json` pins the source/exports, original AddrTop declaration
and body hashes, reviewed scalar fragment, fixture and outputs. Raw generated
Lean files and original process logs are retained in `evidence/`. Package
metadata selects Oak's Lean 4.33.1 and patched lean-sail revision
79b4d08505af29d88b3918f32d29840fae1fa191; generated function bodies are unchanged.
The generator archive is the existing ARM pin, SHA256
26b59bcab2d66e9f220d317dfe45f8b09170ed70e59a824553d6f525134d1ff6.

## Impact audit of the reviewed scalar/ordinary-RET slice

The audit is confined to the previously selected AND/ORR/EOR W0,W0,W1 and
ordinary RET X30 paths in ScalarExecution. It does not clear arbitrary
instructions, PAC returns, other existing Arm exports or the Sail backend.

Structural inspection found:

- `aget_X`, `aset_X` and `ZeroExtend__0`: no guarded-match local update followed
  by an outer read. Their register/width behavior is separately kernel checked.
- `LSL` at shift zero: its selected branch directly returns the input. No
  nonzero-shift callback is reached.
- `ShiftReg` selecting LSL: an ordinary exhaustive enum match returns the
  selected shifted value; the generated branch explicitly returns it.
- Scalar logical result and decoder opcode selection: ordinary exhaustive
  matches explicitly return the result or `(op, setflags)` pair. The existing
  all-input generated-model theorem independently establishes the intended
  common 32-bit arithmetic result.
- Ordinary RET: the target starts from the X30 read, the selected non-PAC arm
  keeps it, and BTypeNext is a direct register write. PAC-only mutable updates
  are outside the admitted route. The generated return-kind, target and
  request-state properties remain explicitly checked.
- The selected original word clauses extract fields and call the field decoders.
  Complete decoder first-match refinement was not proved and remains open.
- Previously documented eager feature-query behavior remains present and bounded
  by the existing read-only success/failure hypotheses. This new finding does
  not remove those obligations.

An independent source-evaluator fixture executes 15 AND/OR/XOR-plus-RET cases:
zero, all ones, signed-bit boundaries and arbitrary dirty upper register halves.
Every case asserts the exact zero-extended X0 result, preserved X1, requested
X30 target, BranchType_RET and BTypeNext=00. It supplies explicit read-only
no-BTI/AArch64/no-PAC query fixtures and a BranchTo request recorder, **not an
architectural BranchTo implementation**. The source compatibility equality
adapter gains an interpreter binding to Sail's generic equality primitive;
no instruction body is changed. All expected results are pinned in the manifest.

**These 15 fixtures and structural inspection are supporting evidence, not a
universal Sail-source/ASL-to-Lean equivalence proof.** The published theorems
remain bounded generated-model claims. Their logical truth alone cannot prove
that a defective exporter preserved the original specification. No general
ASL/Sail-source faithfulness, hardware execution or verified-authority label
is asserted. The unreviewed AddrTop/BranchAddr expansion is excluded.

## Reproduce and retain artifacts

From the repository root, with the pinned official Sail bundle (including z3),
Lean 4.33.1, patched support checkout and pinned Arm source available:

    python3 spec/sail/repros/guarded_mutation/check.py --output-dir /tmp/fresh-audit
    OAK_REQUIRE_ORACLES=1 go test ./asm -run '^TestSailScalarExecutionGuardedMutationAudit$' -count=1 -v

Use a fresh output directory. The script retains sources, raw exports, process
logs and a manifest there. It compares the manifest against the frozen evidence,
checks both reduced cases in the source interpreter and Lean kernel, records
the full-fixture elaboration failure, and reruns all 15 admitted-path source
cases. The required scalar CI lane includes this audit. Passing the audit means
the discrepancy and its scope were reproduced, **not that the bug was fixed**.
Any exporter correction must be tested separately against the source result 55
before the known-discrepancy expectation or proof provenance can be changed.
No upstream issue or PR is created by this test.
