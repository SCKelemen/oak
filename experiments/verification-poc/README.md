# Oak verification experiment — Go implementation

A removable verification experiment in `experiments/verification-poc/`.
The implementation is Go, using Oak's existing checked frontend in process.
There is no Python runtime, duplicate source parser, subprocess frontend, new
language syntax, or production compiler hook. Delete this directory to remove
it. All dependencies are Go's standard library and Oak's existing packages.

## Run

Use the Go toolchain from Oak's `go.mod`. From this directory:

```sh
go test ./...
go build -o build/oak-verify .

./build/oak-verify emit --out build/enum examples/native/enum.json
./build/oak-verify prove-local --out build/enum.proof.json examples/native/enum.json
./build/oak-verify verify examples/native/enum.json build/enum.proof.json
./build/oak-verify closed-set --out build/enum.closed.json examples/native/enum.json

./build/oak-verify trace --out build/counter.trace.json examples/native/counter-broken.json
./build/oak-verify verify examples/native/counter-broken.json build/counter.trace.json
```

You can substitute `go run .` for `./build/oak-verify`. Options precede
positional arguments. `emit` generates files; it does not claim verification.
`prove-local` generates and checks LRAT safety evidence. `closed-set` checks
reachable safety by finite closure, including invariants that are not inductive.
`trace` searches for
and checks a shortest reachable counterexample. Accepting a counterexample
establishes a model bug, not safety; every result names its claim.

The original Boolean models also run through Oak's native frontend:

```sh
./build/oak-verify prove-local --out build/borrow.proof.json examples/borrow.json
./build/oak-verify trace --out build/borrow.trace.json examples/broken.json
```

The branch now supports `&&` and `||`, so these models no longer need the
experimental Python parser. Boolean literal patterns are outside the native
candidate examples; enum and integer matches are supported.

## Model surface

Models use ordinary records, nullary nominal enums, and pure predicate functions.
A JSON project assigns the `source`, `initial`, `step`, and `invariant` roles.
There is no verification keyword or production package configuration.

```oak
Phase: type = | Idle | Reading | Writing | Conflict
State: type = { phase: Phase }
initial: (s: State): Bool = s.phase == Phase.Idle
safe: (s: State): Bool = s.phase != Phase.Conflict
step: (s: State, t: State): Bool = s.phase ? {
  | Phase.Idle => t.phase != Phase.Conflict
  | Phase.Reading => t.phase == Phase.Idle
  | Phase.Writing => t.phase == Phase.Idle
  | Phase.Conflict => t.phase == Phase.Conflict
}
```

Unconstrained next-state fields are nondeterministic; they are not implicitly
unchanged. The temporal model permits stuttering and checks safety. Inductive
safety is stronger than reachable safety. No fairness/liveness is assumed.

The supported fragment has one record with 1–6 fields and at most 16 encoded
state bits. Fields are `Bool`, `u8`, or enums of up to 16 nullary constructors.
Enum equality is nominal; unused bit patterns are excluded by domain guards.
Predicates are pure, nonrecursive Boolean functions over state parameters.
Matches must be exhaustive and cannot bind payloads. Unsupported syntax fails.

Byte literals use `u8(n)`, with `0 <= n < 256`; comparisons are unsigned.
Addition and subtraction require the project option `"arithmetic": "u8-wrap"`,
which explicitly selects modulo-256 **experimental model semantics**. This is
not a claim about compiled Oak's overflow behavior. Local enumeration is
limited to 1,024 states and local proof search to 4,096 nodes.

## Go packages and trust

| Component | Responsibility |
| --- | --- |
| `frontend/` | Export the narrow model from Oak's `Compilation.Check()` result |
| Root command | Typed model, projections, local search, evidence binding, trace replay, external runners |
| `internal/lrat/` | Independent ASCII LRAT RUP/deletion checker; no Oak, encoder, or solver imports |

The evidence checker reconstructs the CNF from the source project. A certificate
cannot replace the obligation, field domains, or assumptions. It checks an
initial-state witness and LRAT refutations of initialization and preservation
counterexamples. Closed-set evidence must include every initial state, admit no
unsafe member, and include all successors; an empty initial set is rejected.
Trace evidence must begin initially, follow legal transitions
or stutter, and end unsafe.

`oak-evidence-3` binds source bytes, project settings, the checked frontend
model, and a Go-adapter semantics version. Earlier certificate identities are
rejected. The migration tests explicitly rebind old fixture identities only
inside tests, then check their original CNF hashes and proof/trace contents.

The trusted base still includes Oak's frontend, the typed adapter, source
binding, CNF translation, evidence/LRAT checkers, Go, and the execution environment.
Trace replay shares the typed model evaluator. LRAT search is untrusted.
The checker supports ASCII RUP additions and deletions; RAT hints, binary LRAT,
extension variables, and general SMT proof formats are explicitly unsupported.

This does not verify the system itself, Oak's compiler, or arbitrary Oak programs.
The ownership examples abstract borrowing; they do not refine compiler bookkeeping.
Migration parity tests are regression evidence, not a formal translation proof.

## External backends

Install the versions in `tools.lock.json`, put Lean, Z3, CaDiCaL, and Java on
`PATH`, and supply the exact SHA-256-pinned TLC jar. No tools are auto-installed.

```sh
./build/oak-verify suite --tla-jar /absolute/path/to/tla2tools.jar --out build/integration
```

The suite covers seven safe/broken enum, byte, and publication models. It checks tool versions,
compiles Lean definitions before checking theorems, runs Z3 obligations and
bounded searches, runs TLC, and independently checks CaDiCaL LRAT proofs.
Z3/TLC counterexamples must replay successfully. Z3 `unsat` is never relabeled
as an independently checked proof. Bounded `unsat` only covers its bound.

Each run has a fresh attempt directory. `report.json` records commands,
exit codes, outputs, tool probes and individual results. Missing tools,
version mismatches, unknown answers, timeouts, and failed checks fail the gate.
The binary exits 0 for success, 1 for invalid input/rejected evidence/search
failure, and 2 for an unsuccessful integration suite. `go run` itself may map
nonzero program exits to its own exit code.

The runner imports trace outputs automatically. To replay a saved output:

```sh
./build/oak-verify import-trace --backend z3 --bound 5 \
  --query build/integration/ATTEMPT/counter-broken/bmc-values.smt2 \
  --receipt build/integration/ATTEMPT/counter-broken/z3-receipt.json \
  --out build/imported.json \
  examples/native/counter-broken.json \
  build/integration/ATTEMPT/counter-broken/z3-output.txt
```

Use the actual attempt directory from the report. For TLC, the query input is
exactly `Model.tla`, one newline, then `Model.cfg`; omit `--bound`. Receipts bind
source identity and query/output bytes to detect accidental stale reuse. They
are not solver signatures; acceptance always replays the states.

The standalone certificate checker is also exposed:

```sh
./build/oak-verify lrat build/enum/base.cnf build/enum/base.cadical.lrat
```

## Validation and migration

[GitHub CI passed](https://github.com/SCKelemen/oak/actions/runs/34091985274)
with `go test -v -race ./...`. `validation-go.json` records that run. All three
experiment packages passed, including the in-process native frontend, CLI,
proof soundness/regression cases, malformed input rejection, trace imports,
and timeout handling.

For all five fixtures, Go's checked frontend document and emitted CNF, SMT-LIB,
TLA+, and Lean files match the captured Python outputs. Their existing LRAT
proofs and traces also validate after explicit test-only identity rebinding.
`testdata/parity/` contains these static fixtures; running tests needs no Python.

The pinned external Lean/Z3/TLC/CaDiCaL suite has now passed in GitHub Actions
across all seven projects (28 backend/project checks). This includes checking
actual CaDiCaL LRAT certificates and replaying actual Z3/TLC counterexamples.
See `validation-external.json` for the tested commit, run, and scope.

The Python implementation and earlier tree/closed-set prototype are preserved
in [Git history](https://github.com/SCKelemen/oak/tree/fa920cd07aaa213feb376a46787c574a58a51a84/experiments/verification-poc).
The current command replaces them with the typed finite model, LRAT, and trace
pipeline, including closed-set checking; it does not accept the old
`oak-evidence-1` certificate format.
The experiment uses the existing production compiler and root dependencies.
Its only root-level addition is the removable opt-in workflow described below.

## Next-stage validation projects

The suite now also includes [bounded release/acquire publication](examples/native/publication.md)
and its weakened-ordering counterexample. Go tests compare the model's reachable
prefixes with Oak's `semir.MemoryExecution` happens-before and race queries.

[Abstract RUP/deletion soundness](proof/README.md) is specified and proved in
Lean separately from the Go implementation. The principal theorem is
`OakVerification.accepted_unsatisfiable`. It does not claim that the Go checker,
its parser, or the source-to-CNF translator has been refined to that specification.
The companion `proof/RUPExecutable.lean` now defines an executable checker for
decoded proof streams and proves `checkProof_sound`. The opt-in gate also checks
Go/Lean decision agreement on a bounded exhaustive and regression corpus; that
agreement is tested, not formally proved. See the proof README for exact scope.

The opt-in workflow is `.github/workflows/verification-poc.yml`. Use its manual
`workflow_dispatch` trigger once available on the default branch, or push a
commit to `specification` whose message contains `[verify-poc]`. Ordinary pushes
skip its jobs and install no solver toolchains. The marker also permits explicit
empty-commit validation runs without changing model files.

The workflow has separate soundness and external-solver jobs. It installs the
pinned toolchains, checks Go regressions and memory-model correspondence, runs
all seven model projects, and retains generated models, solver outputs, proof
certificates, replayed counterexamples, tool provenance, and Lean diagnostics as
30-day artifacts even after a failed check. Lean warnings are errors, so a proof
hole cannot silently turn the soundness job green.

`bash ci/install-tools.sh all` provides the same explicit Linux provisioning;
source `build/tools/env.sh` afterward. Lean and TLC downloads are hash-checked,
CaDiCaL is built from its pinned commit, and the older Z3 release is version-pinned
with its fetched archive hash recorded. The verifier itself never installs tools.
