# Bounded reader/APDU abstract-model gate

This mandatory CI gate compiles the exact two handwritten Lean models and checks their actual theorem/dependency/axiom environment. It establishes abstract-model proof authority under normal official imported-object trust. It does not establish Oak extraction/refinement, physical memory/alias/frame behavior, or FIDO/PIV/OpenPGP/complete ISO conformance. See `docs/verification/reader-apdu-model-evaluation.md`.

## Fixed source and proof contract

`check.py` locks `contract.json` by SHA256. That contract locks both model sources, the exact accepted audit driver, the external consumer/support code and `distribution.json`. The publication commit/review binds `check.py` itself; no self-referential digest is used. There is no update, regeneration, alternate-version or skip mode. An intentional source/tool/expectation update requires review of the changed statements/meaning, explicit contract changes, and the matching constant in check.py. Merely accepting whatever hashes currently exist would remove the statement-preservation boundary.

The exact v2 source identities preserve 48 named theorem statements/bodies and 15 anonymous examples. The audit resolves 46 public and two private theorems using actual module ownership and private-name recovery; it checks declaration kind and proof authority. It does not independently restate theorem types. Thus source identity provides the signature-preservation check. Examples are checked while compiling their source and are not invented as persisted declarations. The locked candidate count is 500, in addition to complete candidate/graph validation.

`AuditDriver.lean` is byte-identical to the accepted corrected local revision03 (SHA256 30766ae03c171245001999ce71073011c1876f94627b0ecb6276307b9c094e9d). `audit_consumer.py` preserves the accepted strict diagnostic/graph logic with path/contract arguments and the added exact-500 rejection bound. `support.py` preserves duplicate-safe JSON/input checks and additionally rejects exponent-overflow nonfinite numbers. The driver compares collectAxioms with checked-body traversal for each named theorem and audits every candidate declaration. The external consumer independently reconciles the shared graph and each of the 48 named theorem axiom sets; it does not independently recompute every candidate-only axiom report.

## Toolchain/import trust

Only official Lean 4.33.1 Linux/amd64 bytes are accepted. `distribution.json` pins 6,289 selected leaves, 1,100,616,161 bytes per authentication pass, derived from official archive SHA256 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235. It includes the executable, Lean shared libraries, source/API authority and all five artifact facets for the 1,047 expected imported distribution modules. Both before and after passes are mandatory. Actual audit imports must equal those modules plus the two fresh models. These pins cannot be reused for another Lean version.

The Ubuntu 24.04 runner, Python standard library and system loader/libraries are additional trusted hosted components. Their identities are not inherited from the local executor's host-library receipt. Official imported objects are authenticated, not freshly kernel-rechecked. The normal aggregate lake build and all existing proof/correspondence steps remain separate required checks.

## Execution and bounds

From repository root, after selecting the repository toolchain:

`python3 -B spec/lean/reader_apdu/check.py --lean "$(cd spec/lean && elan which lean)" --work "$RUNNER_TEMP/reader-apdu-model"`

The work path must be absent. A fresh private object directory is the sole project LEAN_PATH. No cached project object or lake environment is used for this isolated check. Each object is bound by checked descriptor metadata, content hash, owner and private permissions; identical-byte inode replacement is refused. Exact model/driver sources are checked immediately before their relevant invocations and reauthenticated at acceptance.

There are exactly three Lean invocations: reader, APDU and audit. All retain `-j1 -s65536 -M1536 -T200000 -DmaxHeartbeats=200000 -DmaxRecDepth=2048 -DElab.async=false -DwarningAsError=true --json`. The whole ceiling is 480 seconds, initial/final authentication each at most 30 seconds, and phases at most 120/180/120 seconds, clipped to original whole+450 with a five-second internal cleanup reserve. The workflow adds a nine-minute outer step ceiling without enlarging the accepted inner budget.

Hard per-Lean limits are 8 GiB address space, 8 MiB regular files and zero cores. Sampled guards preserve a 2 GiB host-available-memory floor, 2 GiB direct Lean RSS cap, 560 MiB protected free-disk floor and 64 MiB fresh logical/allocated output cap. Fresh-tree enumeration has explicit 64-entry/four-level bounds. These guards do not establish continuous process-tree containment. Audit stdout is captured through bounded parent pipes (12 MiB); each compiler stdout and stderr is capped at 512 KiB. Parent-written audit logs may exceed the child's regular-file cap; that cap is not misrepresented as a parent cap.

Each child has a new owned session/group. The parent uses waitid(WNOWAIT), signals that still-owned group before reaping, always waits the direct child and closes both selector-managed pipes. Acceptance requires exact zero status, complete EOF on both pipes, no overflow and live deadlines. No arbitrary escaped-descendant emptiness or local-supervisor reporting equivalence is claimed. Cleanup/capture failure fails the gate. Evidence includes bounded raw streams, direct execution records and `result.json`; process exit zero and accepted=true are both required.

## Finite controls

`python3 -B spec/lean/reader_apdu/test_check.py -v` runs synthetic consumer and filesystem/metadata controls. Subprocess entry points are patched to refuse; no Lean/toolchain import/build runs. The controls retain cyclic/shared/repeated graph references as valid and reject malformed/missing/duplicate records, wrong identities, unapproved authority, stale/replaced objects, source/contract drift and budget/completion violations. Resource/process completion tests are mocked predicates, not real signal/reap or Lean runtime validation.

The first repository adapter/control revision is source-reviewed only until a separately recorded cheap-control run and hosted exact-source run pass. Historical local model acceptance does not imply this adaptation has executed. Source comments retained inside accepted model/driver bytes record their original candidate status; the evaluation note records the later local acceptance.
