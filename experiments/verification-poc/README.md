# Oak verification projection experiment

A disposable proof of concept: ordinary-looking Oak model declarations in,
Lean / SMT-LIB / TLA+ files out. One folder, no compiler changes, no dependencies
for generation or the local finite-state check. Requires Python 3.10+.

This is an experiment in authoring and projection, **not** a proposed language
extension, an Oak compiler plugin, or a proof kernel. Delete this folder to
remove it. The experiment lives in `experiments/verification-poc/`. No CI, package
configuration, or compiler code is modified; it is not wired into any build.

## New: independent evidence checking (v2)

This revision adds `produce.py` (untrusted example search) and `evidence.py`
(evidence acceptance). The original projection tool is unchanged. There is no
production integration and no additional dependency. Remove this one directory
to discard the experiment.

```sh
python3 produce.py examples/borrow.json --kind inductive --out build/borrow.proof.json
python3 evidence.py examples/borrow.json build/borrow.proof.json

python3 produce.py examples/borrow.json --kind closed-set --out build/borrow.set.json
python3 evidence.py examples/borrow.json build/borrow.set.json

python3 produce.py examples/broken.json --kind trace --out build/broken.trace.json
python3 evidence.py examples/broken.json build/broken.trace.json
```

`evidence.py` returns 0 when the supplied evidence establishes its stated claim,
and 1 for rejected, malformed, mismatched, or unreadable evidence. Accepting a
**counterexample** establishes a bug, not safety. Its JSON output names the
claim explicitly. A positive search report is not accepted as evidence.

Three evidence formats share a source/project/version digest:

| Kind | Checked obligations |
| --- | --- |
| `trace` | Exact Boolean states; initial start; legal transitions (or stuttering); unsafe endpoint |
| `inductive` | Valid initial witness; Boolean refutations of initialization and preservation counterexamples |
| `closed-set` | Nonempty initial set; every initial state included; every member safe; all successors included |

The checker reconstructs obligations from the given project; the evidence
cannot supply a replacement formula, variable domain, or assumption. A closed
set need not be exactly the reachable set: any safe closed overapproximation
containing all initials is sufficient. This version checks closure by exhaustive
finite enumeration, so it offers separation of trust, not a speedup.

The Boolean proof format has only two rules:

1. `{ "false": true }`: the reconstructed counterexample formula must evaluate
   to false under the current partial assignment.
2. `{ "split": "s.reader", "zero": ..., "one": ... }`: check both Boolean
   branches of a permitted variable not already assigned on this path.

Proof leaves use conservative three-valued evaluation: unknown is never false.
The producer currently emits full case trees. This is a small propositional
certificate experiment, **not** LRAT, a general SAT/SMT proof importer, or a
Lean-compatible dependent kernel. No external checker output is automatically
upgraded to independently checked evidence. An adapter could supply these formats
later; the checker would still reconstruct claims from the source project.

Why these rules should be sound: a false leaf excludes every completion of its
partial assignment; a split covers both possible values. Induction over the
proof tree therefore establishes unsatisfiability. This is a design argument,
not a mechanically checked metatheorem.

The trust boundary still includes the shared source parser/type checks/term
expansion, source binding by digest, the new checker, Python, and its execution
environment. The checker has its own evaluator and does not call `produce.py`,
`finite_check`, or the producer's evaluator. It does not yet verify itself,
Oak's compiler, translations to third-party systems, or arbitrary Oak programs.

Pre-generated evidence and rejection examples are in `examples/evidence/`.
`validation-v2.json` records the actual independent CLI checks and expected
outcomes. All **20 tests pass** (10 original, 10 evidence tests), including
missing proof cases, forged leaves, repeated variables, illegal trace edges,
omitted closure states, wrong-source evidence, initial witnesses, duplicate
JSON keys, and exhaustive small-formula evaluator/proof checks. External
Lean/Z3/TLC validation remains unavailable as in the first delivery.

## Try the original projection tool

From this directory:

```sh
python3 project.py check examples/borrow.json
python3 project.py check examples/broken.json
python3 -m unittest -v
```

The first command succeeds. The second deliberately exits 1 and reports:

```text
{reader: false, writer: false}
{reader: true,  writer: false}
{reader: true,  writer: true}
```

The model is deliberately tiny: `reader` means at least one reader, not a
concrete reader count. `release_read` abstracts the last reader releasing.
No correspondence with the compiler's actual borrow bookkeeping is claimed.

## Authoring surface

`examples/borrow.oak` contains one semantic record and ordinary predicate
functions. For example:

```oak
State: type = {
  reader: Bool
  writer: Bool
}

initial: (s: State) -> Bool = !s.reader && !s.writer
safe: (s: State) -> Bool = !(s.reader && s.writer)
```

Transition predicates take old and new state explicitly. Calls compose them
into `step`. Every field of the next state must be constrained when that is
intended; omitting a constraint means nondeterminism, not an implicit unchanged
field. There is no transition or invariant keyword.

`examples/borrow.json` assigns roles outside the language:

```json
{
  "source": "borrow.oak",
  "initial": "initial",
  "step": "step",
  "invariant": "safe"
}
```

The prototype independently parses and checks a narrow subset inspired by
Oak's normative syntax at `specification` commit
`03ac63c17347293e022d038763850f67bd6d3d2e`:

- Exactly one record, with 1–6 Boolean fields.
- Declaration-form functions with individually typed state parameters,
  `-> Bool` or `: Bool`, and `= expression` bodies.
- Boolean literals, field reads, `!`, `&&`, `||`, `==`, `!=`, parentheses,
  and nonrecursive predicate calls (including forward references).
- Whitespace/newlines and `//` comments; optional commas between record fields.

Everything else is rejected, including integers, record equality, imports,
mutation, recursion, arbitrary expressions as state arguments, and unsupported
syntax. The real Oak parser/typechecker is not used or modified. These source
files have **not** been compiled with Oak. The independent parser is a conscious
disposability tradeoff; retain it only as long as useful for this experiment.

## Generate and hand off

```sh
python3 project.py emit examples/borrow.json
```

Outputs go to `build/borrow/` (or `--out DIR`):

| File | Meaning |
| --- | --- |
| `Model.lean` | Boolean definitions and kernel-evaluated case-split proofs of initialization and inductive preservation |
| `initial.smt2` | Initial-state satisfiability; expected `sat` |
| `base.smt2` | Counterexample to initialization; expected `unsat` |
| `step.smt2` | Counterexample to inductive preservation; expected `unsat` |
| `Model.tla`, `Model.cfg` | Finite record-valued transition system, stuttering, type and safety invariants |
| `manifest.json` | Source/config/version digest and translation trust boundary |

There is no copied handwritten model per backend. Predicate calls are inlined
from one checked Boolean tree, and identifiers are mapped to generated names.
Generation invalidates any old `report.json`; generation alone is never a
verification result. Files in the output directory are disposable.

With the external checkers installed:

```sh
python3 project.py check examples/borrow.json --backend z3
python3 project.py check examples/borrow.json --backend lean
python3 project.py check examples/borrow.json --backend tlc --tla-jar /path/to/tla2tools.jar
python3 project.py check examples/borrow.json --backend all --tla-jar /path/to/tla2tools.jar
```

Use the same commands with `examples/broken.json` to exercise failures.
Lean and Z3 must be on PATH. TLC needs Java and a caller-supplied tools jar.
No tool is downloaded or installed by this project. `--timeout SECONDS`
defaults to 30 seconds per external process/query.

You can also invoke the generated files directly:

```sh
lean build/borrow/Model.lean
z3 -smt2 build/borrow/initial.smt2
z3 -smt2 build/borrow/base.smt2
z3 -smt2 build/borrow/step.smt2
java -cp /path/to/tla2tools.jar tlc2.TLC -config build/borrow/Model.cfg build/borrow/Model.tla
```

Apalache is not included as a runner: TLC is enough for the first finite-state
experiment; typed Apalache projection is a later, separate test.

## Results and trust

`check` always runs the independent finite-state explorer, then any requested
external backends. It writes `report.json` and prints the same JSON.

- Exit **0**: every requested check passed.
- Exit **1**: a reachable counterexample or an external check failure occurred.
- Exit **2**: invalid input, unavailable tool, timeout, error, or unknown result.

The finite checker rejects an empty initial set, enumerates the entire Boolean
domain, and performs breadth-first reachability with a shortest counterexample
trace. It also checks inductiveness independently. A reachable invariant can
hold without being inductive; the report preserves that distinction. Deadlocks
are listed but are not safety failures; the temporal model permits stuttering.

Lean/SMT establish the stronger inductive obligations, whereas TLC explores
reachable safety. These methods can disagree on an invariant that needs
strengthening; that is not necessarily a translation bug. Initial-state
nonvacuity is checked by the local explorer and SMT; the generated Lean file
only proves the two implications.

All results concern **this explicit finite model**, not the Oak compiler or
arbitrary concurrent implementations. There are no fairness, liveness,
unbounded-integer, or implementation-refinement claims. The adapter is trusted;
its source-to-backend translation has not been formally proved. Z3 `unsat`
is solver-backed evidence, not an independently checked certificate. External
tool output and exit codes are retained; nonzero Lean/TLC exits may indicate
input/tool errors as well as failed obligations, so inspect their diagnostics.

## Validation performed for this delivery

| Check | Result |
| --- | --- |
| Safe model, complete finite exploration | Passed: 3 reachable states out of 4; inductive |
| Broken model | Expected 3-state counterexample |
| Unit/behavioral tests | 10 passed |
| Generated SMT assertions | Exhaustively evaluated against the source obligations for both fixtures |
| Lean executable | Unavailable; generated file not externally checked |
| Z3 executable | Unavailable; generated file not externally checked |
| TLC tools jar | Unavailable; generated file not externally checked |

Generated `build/` files are ignored; rerun the commands above to recreate
them. `validation-v2.json` records the evidence checks performed for this delivery. The tests cover typing/name/arity rejection, recursion rejection,
operator precedence, exact borrow transitions, counterexample replay,
noninductive but reachable safety, vacuity, deterministic generation, stale
report invalidation, and unavailable/unknown tool results.

## What this experiment lets us decide

1. Do ordinary records and old/new-state predicates feel natural enough?
2. Is keeping the role assignment in a tiny project file sufficient?
3. Are generated models and counterexamples understandable?

If yes, the next small step is using Oak's actual parsed/typed representation
behind the adapter, followed by a carefully scoped integer fragment. If no,
delete the folder; no production interface depends on it.

References: [Oak syntax](https://github.com/SCKelemen/oak/blob/03ac63c17347293e022d038763850f67bd6d3d2e/docs/spec/10-syntax.md),
[Lean](https://lean-lang.org/), [Z3](https://github.com/Z3Prover/z3),
[TLA+ tools](https://github.com/tlaplus/tlaplus).
