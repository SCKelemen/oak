# Certified propagation chain

`PropagationChain.lean` connects the computed clause classifier to a complete
proof-producing RUP chain. It prepares target-negation assumptions in forward
order, tracks compatibility of partial assignments, propagates classified units,
and accepts a classified conflict only at the final hint. Satisfied and unresolved
clauses reject, as do references to absent clauses. Every hint is checked for existence before
contradictory target assumptions may accept.

Successful execution returns a `CertifiedClause` proving that every model of the
database satisfies the target. A successful empty target therefore proves the
database unsatisfiable. A further theorem shows that inserting a certified clause
preserves every database model. These are semantic certificates; this module does
not manufacture a `Propagate` derivation by calling the older checker.

Six reported theorems and three executable definition axiom reports cover
assumption-list restriction, compatible literal writes, assumption refutation
implying target entailment, acceptance entailment, insertion preservation, and
empty-target unsatisfiability. The recursive `prepare`, `chain`, and `check`
definitions carry erased proof fields. Unit steps obtain their premises from the
proved duplicate-aware classifier, not from a semantic oracle or an assumed
unsatisfiability fact. Recursion consumes target literals or hints.

The Go harness calls the uninstrumented Oak `rup_check` through the existing
bounded native runner. The corpus includes the preceding 617 scratch-state cases
and 320 chain cases: ordered chains with 1..64 unit writes, repeated literals,
missing final conflict, nonfinal conflict, and swapped hints. Expected decisions
come from the existing Go RUP checker, with independent assertions for constructed
chain behavior. Lean compares the new certified chain, those decisions, and the
original proof-producing Lean checker on the same bounded input domain.

## Boundary

Soundness of the classifier-based Lean chain is proved for its successful checks.
Equality with the old Lean checker and compiled Oak is tested on the corpus, not
proved universally. The new chain enforces its own positive/bounded target and
used-clause literal checks. The raw Oak kernel relies on its stream caller for
whole-pool validation; malformed or unvisited suffixes are outside this corpus's
comparison contract. Existing range, table, scratch, classifier, text, and actual
certificate gates remain active.

The new checker is isolated and does not replace the existing stream checker or
production Oak implementation. The JSON adapter, Go harness, Oak compiler,
generated C, and C compiler/runtime remain trusted test infrastructure.

Next: connect certified chain results to live-table publication and whole
proof-stream acceptance, preserving the same small removable experiment boundary.

## Validation

[The soundness gate passed](https://github.com/SCKelemen/oak/actions/runs/34232455434/job/102081727926)
on commit `2812b6b9103e95ea66feaf1c3f927629a6a66f76`. All six reported theorems
and the three proof-producing executable definitions passed with warnings as
errors. Their axiom reports contain only standard `propext`, `Quot.sound`, and
`Classical.choice`; there are no proof holes or project-specific axioms.

Oak, Go, the new certified Lean chain, and the original Lean checker agreed on
all 937 cases: 368 accepted and 569 rejected. This includes chains with 64 unit
writes and the deliberate missing, premature, and reordered-hint cases. The
native comparison took 14.03 seconds without the race detector. CI retains the
canonical corpus and proof/comparison logs for 30 days;
`../validation-propagation-chain.json` records the exact tested commit and scope.

The new native comparison also passed with Go's race detector in 20.56 seconds.
The full native suite and existing external/certificate gates passed, including
11 accepted Lean certificates and 22 rejected corruptions, the Boolean proof
bridge, and the invariant-model gate. Those certificate gates still use the
existing stream path; they are regression checks, not a claim that the new chain
has already replaced that path.

Repository CI, standard-library, formal-verification, golden-file, and AArch64
memory-refinement checks all passed on the tested commit. Existing gates, corpus
coverage, and timeout limits were preserved.
