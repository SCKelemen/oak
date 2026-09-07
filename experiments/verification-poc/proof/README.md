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

The next refinement obligation is to prove that every successful Go RUP check
and database update corresponds to this relation. After that, source-to-CNF
translation needs its own semantic preservation theorem. Neither is claimed by
this milestone, and this system is not yet self-verified.
