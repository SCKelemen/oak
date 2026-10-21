# Self-hosted solver v1.0: release contract and roadmap

Reviewed against `336cb0c01e817710ec2b33a229e90ffbf5a84dcf` on 2026-10-21.
The commit above anchors the original inventory. The first-wave update below
records subsequent local implementation; it does not attest a final integration
SHA or green hosted CI.

This is an implementation roadmap and proposed release contract, not a claim
that the current solver is release-qualified. The machine-readable companion
is [the requirements ledger](../proofs/selfhost-solver-v1-requirements.json).
Existing normative behavior remains in [verification](../spec/125-verification.md);
[the verification chain](../spec/126-verification-chain.md) describes proof boundaries.

## What complete means

A release is complete when an operator can reproduce and run the advertised
artifact on every supported target, submit an input in the frozen supported
profile, and trust every settled outcome within explicitly declared assumptions.
Every mandatory gate below must have reviewed evidence attached to the same
release candidate and artifact hashes. Implemented code, differential agreement,
a local theorem, and a whole executable refinement are distinct evidence.
Counting merged PRs or theorem declarations does not measure completeness.

* A positive result entails the original source claim, including hypotheses and
  trap obligations. Constants, exhaustive evaluation and BDD decisions need the
  same semantic justification as certificate-backed decisions.
* A refutation supplies source parameters that actually falsify the claim or
  trigger its specified trap. A model of an abstraction alone is insufficient.
* Unsupported input and resource failure produce an explicit refusal/open/error,
  never a settled theorem. `open` is an acceptable result: this release does not
  promise to decide arbitrary Oak programs.
* Search may remain an untrusted certificate producer. Runtime proof decisions
  must not require Go, an external SAT solver or Lean. Lean remains an offline
  proof/build dependency where declared.
* ARM64, RV64 and Wasm are the target qualification goals. Until whole-solver
  runs and artifact connections are complete, individual compiler fixtures do
  not qualify those targets for this release.

## Name the self-hosting boundary

`-solver self -cross none` currently runs the proof ladder in Oak, but the Go
frontend still validates syntax, types, borrowing and discipline before the
solver sees a private source snapshot. This is an implemented self-hosted
**proof engine**, not yet an independently self-hosted source admission pipeline.
S10 must either close that dependency or freeze an explicitly named checked-input
engine product and its producer contract. The release name and support statement
must identify which boundary is delivered. This decision cannot be silently
resolved by disabling source validation.

## Proposed source profile to freeze in S01

The implementation already covers Bool and fixed-width integers; IEEE bit
patterns and documented abstract operations; scalar leaves of records, fixed
arrays and sums; conditionals and matches; bounded/countable loops; inlined
calls; and supported local-array views. This is a starting inventory, not a
claim that every combination is admitted. S01 must enumerate exact constructs,
widths, builtin operations, limits and negative conformance cases against the
actual parser, serializer and lowering.

Unbounded recursion/loops, general heap mutation, arbitrary aliasing and stores
through views are outside this proposed v1 profile. Floating-point arithmetic
and nontrivial integer division use abstractions in some paths; positive claims
need a sound abstraction relation and negative claims need concrete replay.
Protocol exploration is finite reachable-state checking, not general temporal
logic completeness. Automatic invariant synthesis is not a release requirement.
Unknown constructs must be refused explicitly rather than approximated silently.

## Gates and current position

`in_progress` means a focused slice has an owner in this implementation wave;
it does not mean the whole gate is nearly complete. `open` may have substantial
existing implementation. No gate is marked complete, and this snapshot makes
no claim about fresh CI execution.

| Gate | Required outcome | Status | Depends on |
| --- | --- | --- | --- |
| S01 | Supported semantics and release contract | in_progress | — |
| S02 | Checked serialized input | in_progress | S01 |
| S03 | Allocation and ownership failures | in_progress | — |
| S04 | Source-to-term refinement | open | S01 |
| S05 | Global CNF state invariants | in_progress | S02 |
| S06 | Whole term-to-CNF composition | open | S04, S05 |
| S07 | Authority of every verdict path | in_progress | S04, S06 |
| S08 | Source counterexample reconstruction | open | S04, S06, S07 |
| S09 | Runtime failures and resource limits | open | S02, S03, S07 |
| S10 | Self-hosted admission boundary | open | S01, S02, S04 |
| S11 | Checker executable refinement | open | S07 |
| S12 | Whole solver target qualification | open | S09, S10, S11 |
| S13 | Reproducible bootstrap and artifacts | in_progress | S01 |
| S14 | Performance and search quality | open | S09, S12, S13 |
| S15 | Acceptance composition and release ledger | open | S01, S02, S03, S04, S05, S06, S07, S08, S09, S10, S11, S12, S13, S14 |

## Acceptance evidence and remaining work

### S01: Supported semantics and release contract

**Exit:** Freeze input/source profile, trap and hypothesis semantics, outcome vocabulary, resource policy, runtime dependencies and target list; link positive and negative conformance cases.

**Current:** Planning contract added; source fragment is implemented but no versioned conformance profile is qualified.

**Starting evidence:** [`docs/spec/125-verification.md`](../../docs/spec/125-verification.md), [`docs/spec/126-verification-chain.md`](../../docs/spec/126-verification-chain.md).

### S02: Checked serialized input

**Exit:** Validate framing, dimensions, indices, operand references, graph order, widths and spans before consumers; malformed/truncated/adversarial inputs must fail closed.

**Current:** BDD/CNF input shape guards implemented with 179 truncation cases plus reference and width checks. Variable maps, outer framing and live storage validation remain unchecked parts of the admission boundary.

**Starting evidence:** [`prove/solver/driver.oak`](../../prove/solver/driver.oak), [`prove/solver/lower.oak`](../../prove/solver/lower.oak), [`solver_input_admission_test.go`](../../solver_input_admission_test.go).

### S03: Allocation and ownership failures

**Exit:** Every allocation failure schedule must return a non-authoritative failure, avoid null ownership/dereference, release each successful allocation once, and clear stale verdicts.

**Current:** Shell/certificate null-allocation guards and cleanup implemented; 28 failure masks pass focused tests. Upstream allocations and formal lifecycle composition remain open.

**Starting evidence:** [`prove/solver/shell.oak`](../../prove/solver/shell.oak), [`prove/solver/certify.oak`](../../prove/solver/certify.oak), [`lrat_lifecycle_test.go`](../../lrat_lifecycle_test.go), [`solver_allocation_test.go`](../../solver_allocation_test.go), [`cnf_allocation_test.go`](../../cnf_allocation_test.go), [`solver_allocation_failure_test.go`](../../solver_allocation_failure_test.go).

### S04: Source-to-term refinement

**Exit:** Compose checked source semantics with generated terms, including path hypotheses, traps, widths, signedness, aggregates, calls and loop limits for the frozen profile.

**Current:** Differential corpora exist; whole source-to-term semantic refinement remains open.

**Starting evidence:** [`prove/solver/tree.oak`](../../prove/solver/tree.oak), [`prove/solver/syntax.oak`](../../prove/solver/syntax.oak), [`prove/solver/lower.oak`](../../prove/solver/lower.oak).

### S05: Global CNF state invariants

**Exit:** Establish initialization, freshness, memo/unique reuse, bounded probing and refusal invariants for the actual mutable state and all node constructors.

**Current:** Bounded CNF probing and invalid-entry guards implemented with a 264-case corpus and 16 audited proof closures, including extracted-loop termination. The global mutable-state invariant remains open.

**Starting evidence:** [`prove/solver/cnf.oak`](../../prove/solver/cnf.oak), [`spec/lean/Oak/CNFNodes.lean`](../../spec/lean/Oak/CNFNodes.lean), [`cnf_nodes_test.go`](../../cnf_nodes_test.go).

### S06: Whole term-to-CNF composition

**Exit:** Prove actual term traversal and root obligations preserve satisfiability and justified constant outcomes, including hypotheses, traps and resource refusal.

**Current:** Local gates, folds, obligations, layouts and buffer readback are proved; whole traversal composition remains open.

**Starting evidence:** [`prove/solver/cnf.oak`](../../prove/solver/cnf.oak), [`spec/lean/Oak/CNFObligation.lean`](../../spec/lean/Oak/CNFObligation.lean).

### S07: Authority of every verdict path

**Exit:** Account for constants, exhaustive evaluation, witnesses, BDDs and CNF certificates; only checked sound evidence may settle a row, and contradictory evidence must leave it open.

**Current:** Go cross-check response admission now requires complete, unique rows before evidence is accepted. This covers -cross go; -cross none and whole verdict-path semantic composition remain open.

**Starting evidence:** [`prove/solver/shell.oak`](../../prove/solver/shell.oak), [`prove/solver/certify.oak`](../../prove/solver/certify.oak), [`clause_agreement_test.go`](../../clause_agreement_test.go), [`spec/lean/Oak/LRATRecordSoundness.lean`](../../spec/lean/Oak/LRATRecordSoundness.lean), [`spec/lean/Oak/SATModelSoundness.lean`](../../spec/lean/Oak/SATModelSoundness.lean), [`prove_rows_test.go`](../../prove_rows_test.go).

### S08: Source counterexample reconstruction

**Exit:** Every reported refutation reconstructs typed source parameters and replays the original claim or a trap under its hypotheses; abstract-operation assignments alone cannot refute it.

**Current:** CNF models are checked; end-to-end source reconstruction and abstract-operation replay require qualification.

**Starting evidence:** [`prove/solver/model.oak`](../../prove/solver/model.oak), [`prove/solver/lower.oak`](../../prove/solver/lower.oak), [`docs/spec/125-verification.md`](../../docs/spec/125-verification.md).

### S09: Runtime failures and resource limits

**Exit:** Exercise budget exhaustion, timeout, cancellation, worker death, short or failed I/O and stale output; all outcomes are bounded, correctly classified and preserve evidence rules.

**Current:** Budgets and cancellation exist; systematic failure matrix remains open.

**Starting evidence:** [`prove/solver/shell.oak`](../../prove/solver/shell.oak), [`oaksolver.go`](../../oaksolver.go).

### S10: Self-hosted admission boundary

**Exit:** Either qualify a Go-independent checked-source admission path or explicitly ship a checked-input engine with a versioned producer contract; never label Go frontend validation as fully self-hosted source admission.

**Current:** Self mode has no Go proof decisions with cross none, but Go syntax/type/borrow/discipline validation is mandatory.

**Starting evidence:** [`prove_cmd.go`](../../prove_cmd.go), [`docs/spec/125-verification.md`](../../docs/spec/125-verification.md).

### S11: Checker executable refinement

**Exit:** Connect complete checker entry, control flow, loops, memory accesses, allocations and FFI assumptions to the actual artifact for each claimed target.

**Current:** Selected native bodies, guards, calls and loads are covered; the complete executable chain is open.

**Starting evidence:** [`docs/spec/126-verification-chain.md`](../../docs/spec/126-verification-chain.md), [`lrat_native_test.go`](../../lrat_native_test.go).

### S12: Whole solver target qualification

**Exit:** Run required whole-solver acceptance on ARM64, RV64 and Wasm artifacts; fail on missing runners, skipped required cases or unintended C fallback; record target/toolchain identity.

**Current:** Existing native shell test is ARM64-host restricted; compiler fixtures are not whole-solver qualification.

**Starting evidence:** [`spec_solver_test.go`](../../spec_solver_test.go), [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml), [`.github/workflows/formal.yml`](../../.github/workflows/formal.yml).

### S13: Reproducible bootstrap and artifacts

**Exit:** Pin source, compiler, proof dependencies, flags, target and artifact hashes; reproduce from a clean checkout and reject corrupt/stale cache entries.

**Current:** Solver cache uses content digests and atomic publication. Separate generic buildcache size/mtime identity and unchecked binaries, nonhermetic headers/libraries, release bootstrap and artifact manifests remain open.

**Starting evidence:** [`oaksolver.go`](../../oaksolver.go), [`spec/lean/lean-toolchain`](../../spec/lean/lean-toolchain), [`go.mod`](../../go.mod), [`oaksolver_cache_test.go`](../../oaksolver_cache_test.go).

### S14: Performance and search quality

**Exit:** Define representative deterministic workloads, per-target memory/time budgets and regression thresholds; publish decided/open coverage and distributions at the release SHA.

**Current:** Existing measurements are useful host baselines, not qualified native release budgets.

**Starting evidence:** [`solver_bench_test.go`](../../solver_bench_test.go), [`docs/notes/selfhost-performance-2026-10.md`](../../docs/notes/selfhost-performance-2026-10.md).

### S15: Acceptance composition and release ledger

**Exit:** Attach reviewed evidence and successful required runs to one release commit and artifact set; all mandatory gates close with declared assumptions and no unexplained skips.

**Current:** This ledger records requirements and gaps; it is not evidence of a release passing them.

**Starting evidence:** [`docs/spec/126-verification-chain.md`](../../docs/spec/126-verification-chain.md), [`.github/workflows/formal.yml`](../../.github/workflows/formal.yml).

## First parallel implementation wave

| Owner lane | Gate slice | Change boundary | Integration evidence |
| --- | --- | --- | --- |
| Allocation failures | S03 | Shell and certificate allocations/cleanup | Inject each failure schedule; no stale verdict or null owner |
| Input validation | S02 | Serialized-input admission | Malformed framing/count/reference corpus and valid-input parity |
| CNF probing | S05 | Unique/memo table lookup | Saturated table termination and fail-closed outcomes |
| Verdict checks | S07 | Go driver evidence admission | Forged/conflicting response tests; preserve valid outcomes |
| Cache integrity | S13 | Solver build cache | Content identity, tamper rejection and clean rebuild tests |
| Release contract | S01, S15 planning | This document and requirement ledger | Exact gate IDs, dependency graph and source links |
| Integrator | Cross-lane | Extraction, combined regression runs and PRs | Review, reconcile shared changes, normal merge, record exact SHA |


### First-wave implementation update

Allocation, input admission, verdict admission and cache changes have been
integrated locally. CNF guards and their proof work are integrated locally. The following focused results are not full gate-completion evidence.

| Gate | Implemented slice and focused evidence | Remaining boundary |
| --- | --- | --- |
| S02 | BDD/CNF shape guards; 179 truncations plus malformed references and widths in `solver_input_admission_test.go` | Variable maps, outer framing and live storage |
| S03 | Shell/certificate null guards and cleanup; 28 failure masks in `solver_allocation_failure_test.go` | Upstream allocations and formal lifecycle composition |
| S05 | Bounded probing and invalid-entry guards; 264 cases and 16 audited proof closures in `cnf_nodes_test.go` | Global CNF mutable-state invariant |
| S07 | Complete, unique response rows required for Go cross-check admission; `prove_rows_test.go` | `-cross none` and complete verdict semantic authority |
| S13 | Solver cache content digests and atomic publication; `oaksolver_cache_test.go` | Generic `buildcache` size/mtime identity and unchecked binaries; nonhermetic headers/libraries; release bootstrap |

The parent gate statuses remain `in_progress`, and `completion_evidence` stays
empty. Final integration must record the actual commit and validation results;
no hosted-CI success or target qualification is implied by this update.

These are bounded increments, not six promises to finish the entire corresponding
gates. Each lane owns separate files and a worktree. Shared workflow, extraction,
Lean import and proof-ledger changes pass through the integrator. The existing
A01 architecture, A02 kernel boundary, A03 target interfaces, A04 typechecking
and A05 CI/benchmark/ledger efforts are dependencies to consume, not inventories
to recreate. If A05 lands a canonical ledger, import these stable S01–S15 IDs
there rather than maintain competing release truth.

After this wave, prioritize source/term semantics and global CNF state (S04/S05)
so whole-CNF composition (S06), verdict authority (S07) and counterexample replay
(S08) can close. Runtime failures and reproducibility can proceed alongside
those proofs. Native checker refinement (S11) and required whole-solver target
runs (S12) then supply artifact evidence; performance qualification (S14) uses
those actual artifacts. S15 composes the evidence only after its prerequisites.

## Tracking and completion rules

For each merged increment, record its PR/commit, exact validated commands and
outcomes, affected gate, assumptions and remaining exit criteria. A passing
slice does not automatically mark its parent gate complete. Completion evidence
must identify the release commit, target/artifact where relevant, proof/test
results and reviewer assessment; evidence from an earlier SHA requires an
explicit compatibility review or rerun. Required jobs may not silently skip.

The JSON file is a requirements snapshot, deliberately separate from executable
proof certificates. Its `evidence_paths` locate existing implementation and
proof work; they are not test-run attestations. `completion_evidence` is empty
until a gate's full exit criteria are met. Do not infer readiness from the
number of rows, PRs, or tests. A release review must reconcile this contract
with the actual required CI matrix and published artifacts before setting
`release_ready` to true.
