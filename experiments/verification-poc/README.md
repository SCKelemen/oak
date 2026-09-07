# Oak verification experiment

A removable experiment in `experiments/verification-poc/`. Models use records,
nominal enums, and ordinary predicates; a small JSON file assigns initial,
transition, and invariant roles. No verification syntax or compiler changes are
introduced. Delete this directory to remove the experiment.

## Current milestone: typed models and checked SAT evidence

The third iteration adds:

- A read-only Go bridge through Oak's existing `Compilation.Check()` API.
- A typed finite fragment: `Bool`, nullary nominal enums, and `u8`.
- Lean, SMT-LIB, TLA+, and CNF projections from the same typed model.
- An independent ASCII LRAT checker, plus an intentionally small local proof
  producer. CaDiCaL is the external SAT proof producer; Z3 remains an SMT backend.
- Z3 bounded-model and TLC JSON trace importers that replay candidates before
  accepting counterexamples.
- A pinned external integration suite with explicit failure on unavailable
  tools, wrong versions, timeouts, unknown answers, or failed evidence checks.

**Validation status:** 35 Python tests pass; one Go-dependent differential test
is skipped. Local LRAT proofs and counterexamples are generated and checked.
Go, Lean, Z3, CaDiCaL, and the TLC jar are unavailable in the delivery environment;
network downloads were denied. The Go bridge and external projections have
**not been executed against their toolchains**. Trace-decoder tests use synthetic
fixtures derived from upstream formats, not captured successful external runs.
`validation-v3.json` records the actual checks. The native path is a candidate
integration until its gate passes; it never falls back to the reference parser.

## Try it offline

Python 3.10+ and its standard library suffice. From this directory:

```sh
python3 -m unittest -v
python3 finite.py emit examples/native/enum.json --frontend experimental --out build/enum
python3 finite.py prove-local examples/native/enum.json --frontend experimental --out build/enum.proof.json
python3 verify.py examples/native/enum.json build/enum.proof.json --frontend experimental
python3 finite.py trace examples/native/counter-broken.json --frontend experimental --out build/counter.trace.json
python3 verify.py examples/native/counter-broken.json build/counter.trace.json --frontend experimental
```

`prove-local` constructs LRAT refutations of initialization and preservation
counterexample formulas. The acceptance checker rebuilds each CNF from the
source and checks the proof. Evidence cannot replace the formula, field domain,
or assumptions. A checked initial-state witness prevents vacuous safety claims.
`trace` performs finite breadth-first search; accepting its evidence establishes
an actual model bug, **not** safety. The JSON result names the claim.

The suite contains a safe enum ownership model, a broken ownership model,
a bounded byte counter, a broken counter reaching `4`, and a wraparound model.
The enum model abstracts ownership; it is not a proof of Oak's borrow checker.

## Use Oak's frontend

Run inside the Oak checkout, with the repository's Go toolchain installed:

```sh
go test ./frontend
python3 finite.py emit examples/native/enum.json --out build/native-enum
python3 finite.py prove-local examples/native/enum.json --out build/native-enum.proof.json
python3 verify.py examples/native/enum.json build/native-enum.proof.json
```

All new CLIs default to `--frontend oak`. The bridge checks the program using
Oak, then exports a narrow read-only AST document. The model adapter additionally
rejects effects, recursion, unsupported types and expressions. Source hashes
bind the bridge response; evidence identity also binds the project, frontend,
normalized model, and experimental semantics version. Native and reference
certificates deliberately have different identities.

The bridge was reviewed against `specification` at `657d5a5c`; subsequent changes
through `3028b0fe` did not change its frontend API dependencies. Native tests are
in `frontend/main_test.go`; the existing repository-wide Go test command will
also discover them. No workflow or production compiler file is changed.

The original experiment accepted `&&` and `||`; Oak's current lexer/type checker
does not. Oak's parser also does not currently accept Boolean literal patterns.
Native candidate examples therefore use enum/integer patterns and wildcard
arms. `examples/reference/` preserves Boolean-match encodings solely for offline
comparison with the original truth tables. They are not native Oak examples.

## Model semantics

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

The project file names `source`, `initial`, `step`, and `invariant`. No field is
implicitly unchanged: an unconstrained next-state field is nondeterministic.
The temporal model permits stuttering and checks safety without fairness or
liveness claims. Inductiveness is stronger than reachable safety.

Enum equality is nominal. Unused bit encodings are excluded by explicit domain
guards. `u8` comparisons are unsigned and constants must be explicit `u8(n)`
with `0 <= n < 256`. Addition/subtraction require the project setting
`"arithmetic": "u8-wrap"`; results then wrap modulo 256 in every projection.
This is an **explicit experimental model profile**, not a definition of Oak's
runtime overflow behavior. Oak's type specification requires machine-operation
semantics to be specified separately; translation refinement remains unproved.

The fragment permits one record with 1–6 fields and at most 16 encoded state
bits, enums with up to 16 nullary constructors, and nonrecursive pure Boolean
predicates over the state record. Matches must be exhaustive; captures are
unsupported. Local enumeration is limited to 1,024 states and local proof search
to 4,096 nodes. Larger problems require external search and further engineering.

## Pinned external gate

Install the versions linked in `tools.lock.json` and put `go`, `lean`, `z3`,
`cadical`, and Java on `PATH`. Use the exact TLC jar SHA-256 in that file.
No tools are installed automatically; nothing changes global package state.

| Tool | Pin | Role |
| --- | --- | --- |
| Go | 1.27.1, matching Oak | Native checked-AST bridge |
| Lean | 4.33.1, matching `spec/lean/lean-toolchain` | Compile definitions; prove base/preservation with `bv_decide` |
| Z3 | 4.13.4 | SMT obligations and bounded counterexamples |
| CaDiCaL | 2.1.3 / `f13d74439a5b5c963ac5b02d05ce93a8098018b8` | ASCII LRAT via `--lrat --no-binary` |
| TLC | 1.8.0 jar, SHA-256 pinned | Finite reachable safety and JSON traces; Java 17+ |

The TLC upstream release is a mutable prerelease; the jar digest fixes the
actual artifact used. Binary versions are checked before execution. Version
checks are reproducibility guards, not authentication of a binary.

```sh
python3 backend_suite.py --tla-jar /absolute/path/to/tla2tools.jar --out build/integration
```

The suite checks all five native models, compares native/reference frontend
output, compiles Lean definitions before testing theorem outcomes, checks Z3
initial/base/step obligations and bounded searches, runs TLC, and validates
CaDiCaL certificates. Broken-model Z3/TLC traces must replay successfully.
Lean rejection alone is not accepted as counterexample evidence.

Each attempt gets a fresh directory. `report.json` retains exact commands,
exit codes, stdout/stderr, tool probes, and individual outcomes. Trace receipts
bind source identity, query bytes, and output bytes to prevent accidental stale
reuse; they are not solver signatures. Counterexample acceptance always replays
the actual states and transitions. SMT bounded `unsat` only covers its bound.

Exit 0 means the requested operation/gate succeeded; the evidence CLI names
whether the accepted claim is safety or a counterexample. The integration suite
exits 2 for any failed or unavailable check. The other new CLIs exit 1 on
rejected evidence, invalid input, unavailable tools, or search failure.
`--frontend experimental` enables a separate offline-parser integration run;
it does not validate Oak's frontend.

## Trust boundary and limits

`lrat.py` depends only on Python's standard library and is independent of the
source adapter, translator, and proof producer. It checks ASCII RUP additions
and deletions and requires an established empty clause. Negative RAT hints,
binary LRAT, general SMT proof formats, and extension variables are explicitly
unsupported. This restricted format targets the pinned CaDiCaL producer;
actual interoperability is still an external validation gate.

The full claim still trusts Oak's frontend (or the explicit reference parser),
the typed-model adapter, source binding, CNF translation, LRAT checker, Python,
and execution environment. Trace replay shares the typed model's evaluator.
Translation equivalence tests are testing evidence, not a refinement proof.
This system does not verify itself, Oak's compiler, or arbitrary Oak programs.

Z3 `unsat` is solver-backed evidence; it is never relabeled as independently
checked LRAT. Native Oak self-hosting, a verified kernel, dependent type theory,
Apalache, liveness/fairness, unbounded theories, and compiler refinement remain
future work. The next gate is to run the pinned suite on a provisioned machine
and resolve any frontend/projection incompatibilities before expanding scope.

## Earlier experiments remain available

The original Boolean projector and the v2 tree/closed-set checker are unchanged:

```sh
python3 project.py check examples/borrow.json
python3 produce.py examples/borrow.json --kind inductive --out build/borrow.v1.json
python3 evidence.py examples/borrow.json build/borrow.v1.json
python3 produce.py examples/borrow.json --kind closed-set --out build/borrow.set.json
python3 evidence.py examples/borrow.json build/borrow.set.json
```

Their source files use an independent Oak-inspired parser. Historical evidence
is in `examples/evidence/` with `validation-v2.json`. New evidence uses
`oak-evidence-2`; it is intentionally separate from their `oak-evidence-1` format.

Sources: [Oak type semantics](../../docs/spec/20-types.md),
[CaDiCaL LRAT tracer](https://github.com/arminbiere/cadical/blob/rel-2.1.3/src/lrattracer.cpp),
[TLC JSON trace format](https://github.com/tlaplus/tlaplus/blob/v1.8.0/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/_JsonTrace.tla),
[LRAT resources](https://github.com/marijnheule/drat-trim).
