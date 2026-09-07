# Invariant certificates for Boolean Oak projects

The experiment can now export the predicates of a checked Oak project and check
an invariant certificate for the resulting Boolean transition model. No new Oak
syntax, compiler hooks, or mandatory Lean runtime dependency are introduced.

From the experiment directory, with the pinned tools installed:

```sh
go run . export-boolean --out build/model.json examples/native/publication.json
bash ci/check-boolean-models.sh
```

The first command only exports a model; it makes no verification claim. The second
runs the complete example gate: exports both publication projects, builds the Lean
modules, emits obligations, invokes CaDiCaL, and independently checks the proofs.
It records fresh results under `build/boolean-models/`.

## Specification and theorem

`BooleanSafety.lean` defines a model by three Boolean expressions: initial states,
allowed transitions, and an invariant. States are Boolean assignments indexed by
natural numbers. A transition expression uses input `2*i` for current field `i`
and `2*i+1` for next field `i`. Initial and invariant expressions use input `i`.
The `eval_rename` theorem proves that substituting input indices preserves evaluation.

The checker reconstructs two expressions:

- Base violation: `initial(s) && !invariant(s)`.
- Preservation violation: `invariant(s) && step(s,t) && !invariant(t)`.

`checkSafety_sound` proves that if both refutations are accepted, every state
reachable from an initial state through finitely many allowed transitions satisfies
the invariant. The proof composes the Boolean encoding/checker theorem with
induction over reachability. Its path length is unbounded; this is an inductive
invariant result, not a bounded search result. It establishes safety only, not
liveness, fairness, termination, or absence of deadlock.

`BooleanModel.checkTexts_sound` connects successful LRAT text checking to that
same reachability theorem for the decoded model. Checking reconstructs both CNFs
from the model rather than reading back the solver's DIMACS files. Solver search
is outside the trusted mathematical argument.

An empty initial-state set makes safety vacuous. The example gate separately
requires CaDiCaL to report satisfiable initial states for both examples, but that
status is not itself a proved initial-state witness or a premise of the theorem.

## Interchange boundary

`export-boolean` uses the existing native Oak frontend and finite-model validator.
All state fields must be `Bool`. Function calls are already expanded by the model
loader. Boolean equality, inequality, and conditionals are lowered to constants,
inputs, NOT, AND, and OR. Numeric and enum state fields are rejected.

The `oak-boolean-model-1` JSON bundle contains ordered field names, source and
semantic digests, and three postorder expression programs. Programs use backward
references and the final node is the root. The Lean adapter checks the format,
field count and uniqueness, supported operators, input bounds, and program size.
It also limits expanded expression size so shared references cannot create an
exponentially large logical tree. Limits belong to the adapter, not the theorem.

To use an exported bundle directly, first compile the prerequisite modules (the
gate script shows their order), then run:

```sh
lean --run proof/BooleanModel.lean emit build/model.json base build/base.cnf
lean --run proof/BooleanModel.lean emit build/model.json step build/step.cnf
# Supply independently generated ASCII LRAT files for the two queries.
lean --run proof/BooleanModel.lean check build/model.json build/base.lrat build/step.lrat
```

The final command emits a structured result whose scope is
`decoded-boolean-model`. Digests identify the export but are untrusted metadata
when a bundle is supplied independently. Acceptance does not prove that a bundle
matches an Oak file. The parser, typechecker, exporter, and Boolean desugaring still
need correspondence proofs. Exhaustive tests compare exported predicate evaluation
with the existing finite-model evaluator; those tests are evidence, not refinement
theorems. Running Lean code also trusts its compiler and runtime.

## Regression gate

The ordered publication model must pass both obligations. The relaxed model must
fail preservation. Its base obligation still holds, so rejecting it specifically
exercises the need for a checked step obligation. The gate also rejects the safe
model's proofs against the relaxed model, an unjustified suffix appended to each
of the two proofs independently, and malformed programs with forward references, out-of-domain inputs, or
excessive expression expansion.

Negative proof tests require both the expected exit code and a structured checker
rejection; compilation failures cannot pass them. Source bundles, emitted CNFs,
proofs, hashes, diagnostics, and receipts are retained with CI artifacts. Every
attempt starts with a failed report, preventing stale success after a failed retry.

All additions remain in the removable verification experiment. This milestone
adds a formally specified transition model and checked invariant reasoning; it
does not claim a self-hosted Oak kernel or a verified Oak implementation yet.
