# Propagation scratch state

`PropagationState.lean` models a zero-based partial assignment and its byte
representation: 0 means unassigned, 1 false, and 2 true. Logical assignment indices
remain one-based. Ten reported theorems cover representation round trips, stores,
unaffected cells, empty assignments, compatible assignment extension, falsified
literals, clause conflict, forced unit literals, and unit assignment preservation.

A clause whose literals are all false cannot be satisfied by any assignment
extending the scratch state. If all literals except one are false, a satisfying
extension must make that remaining literal true; storing it preserves compatibility.
These theorems require positive logical indices and the stated classification
premises. They do not assume the formula is unsatisfiable.

The Go harness observes test-generated copies of the actual Oak `rup_check` after
hint prevalidation, each attempted target assumption, and each attempted hint.
Every observation includes all 64 bytes plus validity, contradictory assumptions,
and final-hint conflict flags. Cells start poisoned with 7: the variable prefix
must reset and the unused suffix must remain unchanged. Exact trace lengths and
six deliberately corrupted observations check the observer itself.

The corpus includes the existing 400 RUP cases, both polarities at all 64 variable
boundaries, all nonempty target sequences of length at most three over two
variables, and invalid variable/literal and nonfinal-conflict cases. The Go oracle
uses a logical assignment map and literal sets, then serializes the byte state.
It also checks final acceptance against the existing Go RUP checker. Lean executes
an independent functional-cell trace model and compares all observations.

The generated native cases use the existing bounded batch runner. Production Oak
source, syntax, and compiler behavior are unchanged. The harness remains Go.

## Boundary

The semantic lemmas and representation equations are proved in Lean. The complete
bounded trace executor, duplicate-literal classification loop, and Oak array
accesses are compared on the corpus, not universally refined by these theorems.
The corpus uses complete structured clauses and targets with valid descriptors;
raw malformed range descriptors remain covered by preceding range/table gates.
No claim is made that an unvisited invalid literal suffix is validated by this
kernel; the stream caller validates the whole literal pool. Text decoding and
compiler correctness remain separate proof boundaries.

The [clause-classifier milestone](ClauseClassifier.md) now derives those premises
from a functional duplicate-aware classifier and compares it with the actual Oak
scan. Complete propagation-chain refinement remains the next composition step.

## Validation

[The soundness gate passed](https://github.com/SCKelemen/oak/actions/runs/34227481489/job/102065051526)
on commit `99736f3e8d343722938d340de54c2c4360b7e97e`. All ten reported theorems
passed with warnings as errors and no proof holes or project-specific axioms.
Two use no axioms; the remaining reports use only `propext` and/or `Quot.sound`.

Oak, Go, and Lean agreed on all 617 cases and 1,649 complete snapshots (105,536
cell observations plus all control flags and exact trace lengths). Final results
were 239 accepted and 378 rejected; all six observer corruptions were rejected.
The native comparison took 6.20 seconds without the race detector. The canonical
JSON corpus and proof/comparison logs are retained with the soundness artifact
for 30 days. `../validation-propagation-state.json` records the exact scope.

The native comparison also passed with Go's race detector in 9.86 seconds. The
full native suite, external verification suite, Oak ASCII replay (one accepted,
two corruptions rejected), Lean certificate gate (11 accepted, 22 corruptions
rejected), Boolean proof bridge, and Boolean invariant-model gate all passed.

Repository CI, standard-library, formal-verification, golden-file, and AArch64
memory-refinement checks also passed on the tested commit. No existing gates,
corpus cases, or subprocess timeout limits were removed or relaxed.
