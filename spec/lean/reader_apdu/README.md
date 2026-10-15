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

## Qualified reader extraction and generated-definition refinement

The independent `reader-refinement` formal job adds a fixed sibling profile;
`check_refinement.py` reuses the exact locked process, file, storage and official
Lean distribution helpers in `check.py` and `support.py`. The original reader/APDU
abstract-model gate, its contract, its 48 theorem/15 example obligations, and its
limits remain mandatory. There is no mutable profile switch or update mode.

The new job requires all four portable reader/APDU roots through the existing
`required_backend_tests.py reader-apdu` equipped runner. Every selected skip or
failure, absent required root and duplicate run is refused. Normal compiler shards
continue selecting the same four roots. The tests require `cc`, interpreter result
42 and host executable result 42; they do not establish compiler correctness.

Next, the current checkout builds the three explicit Go files under
`.github/scripts/reader_refinement` using Go 1.27.1. This hidden directory is outside
ordinary `./...` and native inventory discovery, so the explicit CI invocation is
necessary. The direct test binary must pass exactly 62 controls, with no children
or skips, before the one `TestBoundedReaderExtractionEmit` root runs. Its actual
qualified loader, public checks and `EmitLeanRoots` must produce all three exact
accepted outputs. The outer profile verifies raw and profiled byte equality,
complete receipt equality, four current original-source pins, twelve source spans,
and sixteen generated declaration spans. Only the two original header budget
reductions are accepted; no generated body is replaced.

The receipt's `tree_requires_outer_authentication` remains the historical
`a86fe4f8a36fd5687282907c1e6b8f95154ff0f0` extraction-profile authority. It is not
relabelled as the new integration tree. Checkout `HEAD == GITHUB_SHA`, unchanged
tracked source during the build, the fixed source contract and fresh build are
separate hosted authorities for the current source. Relevant original source,
fixture, extraction and helper bytes are locked. The complete compiler/build,
qualified loader, checker and extractor remain in the trusted computing base.

The profile compiles `BoundedReaderModel`, `BoundedReaderExtracted` and
`BoundedReaderRefinement` freshly into a private three-object import root, then
runs the exact accepted `RefinementAuditDriver.lean`. Full private-name records
and independent dependency traversal must reconcile 117 named propositions
(including 18 named controls), 753 owned declarations and 1,050 imported modules.
The latter comprises three candidate modules plus the exact 1,047-module official
Lean 4.33.1 closure. Only `propext`, `Quot.sound` and `Classical.choice` are allowed;
no admission, reduction oracle, missing declaration, diagnostic or incomplete
capture is accepted. These counts belong only to the locked source/toolchain.
Future source changes require a reviewed lock update, not automatic regeneration.

The imported proof/driver comments retain their original source-candidate wording to
preserve the exact accepted bytes. The later local terminal evidence is recorded
in `docs/verification/reader-apdu-model-evaluation.md`; it supersedes those historical
uncompiled-status comments without transferring a hosted pass.

The accepted theorem scope is the generated Lean definitions: total window,
remaining, take and big-endian-word equations, explicit error priority, lossless
UInt-to-Nat projections, safe array indices, nonwrapping arithmetic, byte values
and returned cursor state. Extractor correctness, the Oak operational load trace,
physical alias/frame behavior and emitted C/machine behavior remain open.

### Time, storage and hosted trust

The standalone Go build has a 300-second external timeout, one build worker,
80 MiB regular-file limit and an 80 MiB accepted test-binary ceiling. Go's 1,536 MiB
`GOMEMLIMIT` is advisory. Setup-Go, its normal module/build caches and Ubuntu build
processes are trusted hosted facilities; this is not a local donor-cache or
whole-process-tree memory-isolation claim. The portable four-root step has the
existing runner's 10-minute Go timeout and a 12-minute CI step ceiling.

The refinement wrapper has one 600-second deadline: at most 30 seconds initial
binding, 60 shared seconds for the two Go invocations and output verification,
four serial 120-second Lean phases, and 30 seconds final binding/publication.
Every phase is clipped to the original deadline with final reserve. Lean flags
stay `-j1 -s65536 -M1536 -T200000 -DmaxHeartbeats=200000
-DmaxRecDepth=2048 -DElab.async=false -DwarningAsError=true --json`.
The inherited hard limits are 8 GiB address space, 8 MiB child regular files and
zero core dumps, with sampled 2 GiB direct RSS/host-memory guards and a 560 MiB
free-disk floor. Private fresh logical and allocated output is capped at 64 MiB.
The separate prebuilt Go binary is outside that 64 MiB allowance. Direct owned
process groups are signalled, direct children reaped and capture completed;
arbitrary escaped-descendant emptiness is not established. The 35-minute job
ceiling includes tool setup, controls, portable checks, build, proof and upload.
These are conservative refusal limits, not measured hosted completion forecasts.

### Retained evidence and replay

Only successful adapter and pre-upload verification steps may upload the seven
literal files: `audit-stdout.log`, empty `audit-stderr.log`, `result.json`,
`object-hashes.json`, and `extracted/{raw.lean,BoundedReaderExtracted.lean,extraction.json}`.
The artifact is named by commit/run/attempt and retained for 14 days. Its maximum
accepted content is 12,845,056 bytes: 12 MiB audit, two 32 KiB metadata files and
three 64 KiB extraction files. Objects, caches, environment and unused failure
logs are excluded. A late finalization failure can leave accepted-looking result
bytes; the failed adapter step still blocks upload.

For independent replay, authenticate the retained manifest and source contract,
then call `refinement_audit_consumer.diagnostics` with the complete retained audit
streams, phase `audit`, the exact `audit_driver_path` recorded in the manifest,
the locked contract and a fresh finite consumer deadline. This rechecks every
record and dependency edge. `verify_retention` is a byte/coherence preflight, not
full graph replay or object rechecking. Object hashes are receipts; they do not
replace recompilation. The Ubuntu runner, Python, loader/libraries and build
facilities are trusted separately from the exactly hashed official Lean files.


## Qualified APDU extraction and generated-definition refinement

The fixed `apdu-refinement` job preserves reader117 and abstract-model48 gates.
It builds the three explicit Go files in `.github/scripts/apdu_refinement`,
requires 70 named controls and one actual extraction, and compares complete raw,
profiled and receipt bytes. Five current Oak files, two fixtures, 25 original
source spans and 30 generated spans are authenticated. Only the two accepted
header budget changes are permitted. Receipt tree
`b62ada7603f8311e2d25cf135a04464b4eb24323` is historical; current checkout/build
and source locks are separate authorities.

`check_apdu_refinement.py` freshly compiles all eleven pinned modules in the
contract's topological order into a private object root, then invokes the exact
accepted `APDURefinementAuditDriver.lean`. The independent consumer requires 280
named theorems, 15 anonymous examples checked by exact source compilation, 41
named controls, 2,226 candidate declarations and 1,058 imports. It reconstructs
complete graph coverage and each named theorem's reachable axioms. Only
`propext`, `Quot.sound` and `Classical.choice` are allowed. The 100,000-edge cap
remains fixed; local acceptance observed 99,722 edges, leaving 278. Drift fails
closed and requires review. Existing117/48 obligations remain mandatory.

`APDUParserCorrectness.decode_eq` relates the generated Lean root to the complete
header/length model for arrays smaller than 2^32 and any fuel. Inputs longer than
65,544 remain in its rejection domain. This is generated-definition refinement
plus current extraction-byte equality. It does not prove the extractor, Oak
operational semantics, physical alias/frame behavior, emitted C or machine code,
or whole-protocol conformance. Historical source-only comments remain unchanged.

### APDU bounds and retained evidence

Go build limits remain 300 seconds and 80 MiB. One 1,560-second wrapper deadline
covers 30 initial seconds, 60 shared controls/extraction seconds, eleven compile
phases and one audit at up to 120 seconds each, and 30 final seconds. Phases retain
cleanup/final reserves. The proof step has a 27-minute ceiling and the job 45
minutes. These are refusal ceilings, not measured hosted completion forecasts.
All existing Lean flags, 8-GiB direct address-space, 8-MiB child file and zero-core
limits remain. Sampled guards retain 2-GiB direct RSS/host-memory thresholds,
a 560-MiB free-space floor and 64-MiB fresh logical/allocated output cap. They do
not establish continuous process-tree containment or escaped-descendant emptiness.

Accepted work has exactly 64 entries: 42 phase stream/receipt files, 11 objects,
three extraction files, two result/manifest files and six directories. There is
no auxiliary slack. Direct exclusive writes create no temporary rename files.
Archive packaging/additional manifests belong outside this tree. Unexpected or
transient entries fail the existing cap; bounded cleanup evidence does not make
the sampled guard a continuous filesystem quota. A local eleven-object checker
leaves the shared three-object checker unchanged.

Execution and pre-upload verification must both succeed before seven literal
files are retained: audit stdout, empty audit stderr, result, object-hash manifest
and three extraction outputs. Maximum accepted content is 12,845,056 bytes
(12-MiB audit, two 32-KiB metadata files and three 64-KiB outputs), with 14-day
retention and commit/run/attempt naming. No objects or caches are uploaded.
`apdu_refinement_audit_consumer.diagnostics` replays the complete retained audit
using the manifest's driver path and locked contract. Retention preflight alone
is not graph replay; object hashes are receipts, not object rechecking.

October14 local acceptance used eight authenticated existing objects and three
newly promoted objects. It does not establish this all-source hosted rebuild.
This integration is source-only until separately recorded controls, current
extraction, fresh eleven-module compilation, audit and retained replay pass.
Official Lean4.33.1 imports retain ordinary imported-object trust; Ubuntu, Python,
system loader and the current Go build are separate hosted trust components.
