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

For the Go implementation, the outstanding refinement obligation is to prove that every successful RUP check
and database update corresponds to this relation. After that, source-to-CNF
translation needs its own semantic preservation theorem. Neither is claimed here, and this system is not yet self-verified.

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
