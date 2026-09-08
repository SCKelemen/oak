# Abstract RUP/deletion soundness

Run with the experiment's pinned Lean version:

```sh
lean -DwarningAsError=true proof/RUPSoundness.lean
```

`RUPSoundness.lean` defines literals, assignments, clauses, an ID-indexed clause
database, and an abstract acceptance relation. Its rules inspect literal and
clause membership. They do not assume the desired entailment or unsatisfiability.

| Rule | Required justification |
| --- | --- |
| Contradictory assumptions | A literal and its complement are both assumed |
| Conflict | A live hinted clause has all its literals falsified; this is the final hint |
| Unit propagation | A live hinted clause has one candidate literal and every other literal falsified |
| Addition | Propagation under the negated target clause derives conflict |
| Deletion | Remove clause IDs from the active database |
| Acceptance | A checked prefix establishes an empty clause |

The main theorems prove:

- `propagation_sound`: a model of the active database cannot satisfy assumptions
  under which the propagation derivation reaches conflict.
- `rup_entails`: every model of the database satisfies a RUP-derived clause.
- `step_preserves` / `steps_preserve`: additions and deletions preserve every
  model of the initial database.
- `accepted_unsatisfiable`: an accepted abstract refutation implies that the
  initial database has no satisfying assignment.

An empty clause may subsequently be deleted without invalidating the already
established refutation. The specification treats acceptance as the existence of
that checked prefix. The Go implementation additionally validates the remainder
of its input stream.

This is a soundness proof of a **rule specification**, not an executable checker
correctness theorem. It intentionally omits restrictions that only reject more
proofs: increasing/fresh IDs, resource limits, and live hints on tautological
additions. It does not model ASCII parsing, Go maps, integer conversion, source
identity, or the CNF encoder. It supports neither RAT nor theory lemmas.

The file declares no project-specific axioms and contains no proof holes. It
prints the kernel assumptions of its principal theorems. Classical logic is
used when deriving clause satisfaction from contradiction.

For the Go implementation, the outstanding refinement obligation is to prove
that every successful RUP check and database update corresponds to this relation.
After that, source-to-CNF translation needs its own semantic preservation theorem.
Neither is claimed here, and this system is not yet self-verified.

## Executable refinement

`RUPExecutable.lean` adds a terminating, proof-producing checker for **decoded**
RUP additions and deletions. `checkRUP_sound` connects successful RUP checks to
`Propagate`. `checkProof_sound` proves that `checkProof = true` implies an
unsatisfiable initial clause database. Its proof fields are erased at runtime.
Neither theorem takes an assumed correspondence with the Go program as a premise.

The algorithm checks live positive hints before tautology acceptance, rejects
already-satisfied hints, searches for a unit literal, and requires conflict to
be the final hint. Full streams track increasing addition IDs, validate deletion
references sequentially, preserve an established contradiction after deletion,
and reject invalid suffixes even after deriving the empty clause. Duplicate
literals have set semantics. The implementation favors a small proof over speed:
unit search scans lists and database updates use functional lookup closures.

The opt-in workflow compares the Go and Lean decisions using a generated JSON
corpus. It exhausts the one-variable/two-clause RUP domain for hint chains of
length zero through three, including invalid IDs and RAT hints, then adds seeded
larger examples, nontrivial unit chains, and decoded stream regressions. Every
accepted Go decision is independently checked by an exhaustive truth table.
`RUPCompare.lean` is the test adapter; its JSON decoder is outside the theorem.

To run the same checks from the experiment directory after provisioning Go and
Lean:

```sh
mkdir -p build/soundness
export LEAN_PATH="$PWD/proof"
lean -DwarningAsError=true -o proof/RUPSoundness.olean proof/RUPSoundness.lean
lean -DwarningAsError=true -o proof/RUPExecutable.olean proof/RUPExecutable.lean
export OAK_LEAN_DIFFERENTIAL_OUT="$PWD/build/soundness/cases.json"
go test -count=1 -v ./internal/lrat -run '^TestLeanDifferentialCorpus$'
lean -DwarningAsError=true --run proof/RUPCompare.lean "$OAK_LEAN_DIFFERENTIAL_OUT"
```

This closes the abstract-to-executable proof boundary **for the Lean checker**.
Agreement tests do not prove refinement of Go maps, loops, arithmetic, or parsing.
The Lean theorem accepts natural-number IDs and decoded literals; it does not
verify the Go parser's signed-integer limits, byte limits, or DIMACS domain checks.
The source-to-CNF encoder also remains outside the proof. The next formal step
is a semantics-preserving connection to the implementation used by Oak, or an
explicit decision to use this Lean checker as an independent certificate gate.

[The executable soundness and agreement gate passed](https://github.com/SCKelemen/oak/actions/runs/34131061664/job/101771025913):
13,019 cases, with 610 accepted and 12,409 rejected by both checkers.
`../validation-refinement.json` records the tested commit, theorem assumptions,
corpus scope, and remaining proof boundaries.

## Independent certificate gate

`RUPText.lean` decodes ASCII DIMACS and the supported ASCII LRAT subset directly,
without calling the Go parser. It checks declared variable bounds and clause
counts, zero terminators, signed integer limits, and the complete proof stream.
`RUPCheck.lean` exposes it as an isolated file checker:

```sh
export LEAN_PATH="$PWD/proof"
lean -DwarningAsError=true -o proof/RUPText.olean proof/RUPText.lean
lean -DwarningAsError=true --run proof/RUPCheck.lean FORMULA.cnf PROOF.lrat
```

Compile the two prerequisite modules as shown above first. The command prints
one JSON result; status zero means acceptance and status one with a structured
result means rejection. Usage errors, compilation failures, and I/O exceptions
are not certificate results.

The new `checkText_sound` theorem states that successful text checking implies
unsatisfiability of **the database returned by `parseDIMACS`**. It connects the
wrapper to the proved checker, but does not prove that parsing preserves the
external DIMACS meaning. Both the parser and source-to-CNF translation remain
trust boundaries. ASCII whitespace and decimal integers are the adapter's
supported lexical scope; Go's broader Unicode whitespace behavior is not claimed.

After the external suite succeeds, the opt-in solver job runs
`bash ci/check-certificates.sh`. It independently accepts every real UNSAT
certificate recorded by the suite, then requires rejection of each certificate
against its project's satisfiable initial query and rejection of an appended,
syntactically valid but unjustified empty-clause addition. The latter rejection
must occur in the checker, rather than the parser. The gate requires structured
results and exact exit codes, so a tool crash cannot pass a negative test.

The gate checks that all expected certificates were visited, records SHA-256
hashes of the original CNF/proof pairs, and retains the acceptance and rejection
outputs under `build/lean-gate/`. It runs explicitly after the Go `suite` command;
the normal verifier does not acquire a runtime Lean dependency.

`RUPTextCompare.lean` compares text acceptance with Go on the decoded stream
corpus plus hand-labelled malformed and valid text cases. To reproduce it,
set `OAK_LEAN_TEXT_CORPUS_OUT` alongside `OAK_LEAN_DIFFERENTIAL_OUT` when running
`TestLeanDifferentialCorpus`, then pass that JSON file to
`lean -DwarningAsError=true --run proof/RUPTextCompare.lean`.

[The real-certificate gate passed](https://github.com/SCKelemen/oak/actions/runs/34141167226):
11 certificates accepted and 22 corruptions rejected by the checker. The text
corpus also agreed on all 2,571 cases (145 accepted, 2,426 rejected), alongside
the existing 13,019 decoded cases. `../validation-certificate-gate.json` records
the tested commit and remaining boundaries. Failed retries replace any earlier
success report before validating new input.

## Boolean source-to-CNF specification

[BooleanCNF.lean](BooleanCNF.md) specifies the logical Tseitin encoding for
constants, inputs, NOT, AND, and OR, with soundness and completeness theorems.
Its symbolic auxiliary names keep numbering and Go optimizations outside the
proof. The opt-in gate compares the Lean specification and the actual Go
initial-query encoder on exhaustive small expressions and deeper regressions.

## Numbered Boolean proof bridge

[NumberedCNF.lean](NumberedCNF.md) proves that numeric allocation preserves CNF
satisfiability and connects the Boolean source expression to the proved checker.
Acceptance implies unsatisfiability of the expression, or validity when checking
its negation. The opt-in solver job exercises this path with real CaDiCaL proofs
and rejects satisfiable targets and corrupted certificates. Go allocation and
the Oak frontend remain outside the theorem.

## Boolean transition safety

[BooleanSafety.lean](BooleanSafety.md) proves reachable-state invariance from
accepted base and preservation refutations. `BooleanModel.lean` reconstructs the
obligations from a bounded Boolean model export and checks the two proof streams.
The opt-in solver gate exercises safe and relaxed publication models from Oak.

## Oak-resident RUP kernel

[SelfHostedRUP.md](SelfHostedRUP.md) describes the first certificate-checking
kernel written in Oak. It checks one bounded decoded RUP addition using only
caller-owned storage. A deterministic corpus compares the compiled Oak result
with the Go checker and the proved Lean checker.

[SelfHostedStream.md](SelfHostedStream.md) extends it to complete bounded decoded
streams: live-clause state, fresh increasing IDs, checked deletion, and persistent
refutation. The native Oak checker is compared with Go and Lean on 425 streams,
with separate malformed-layout and resource rejection tests.

[SelfHostedText.md](SelfHostedText.md) adds bounded ASCII DIMACS/LRAT decoding in
Oak, text-level Go/Lean comparisons, resource-boundary tests, and replay of an
actual solver certificate. Universal refinement of the Oak implementation
remains unproved.

[MatchLowering.md](MatchLowering.md) records the compiler correction prompted by
the ASCII decoder: Boolean statement guards evaluate once and statement matches
select only one arm. Native regressions and the parser corpus cover the fix.

[BoundedDecimal.md](BoundedDecimal.md) proves the bounded decimal model equivalent
to unbounded decimal evaluation with a final magnitude check, along with
nonwrapping arithmetic, range/cursor guards, and bounded-prefix append
invariants. A separate Go/Oak/Lean corpus compares actual token parsing.
