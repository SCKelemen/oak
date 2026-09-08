# Certified propagation chain

`PropagationChain.lean` connects the computed clause classifier to a complete
proof-producing RUP chain. It prepares target-negation assumptions in forward
order, tracks compatibility of partial assignments, propagates classified units,
and accepts a classified conflict only at the final hint. Satisfied and unresolved
clauses reject, as do missing hints. Every hint is checked for existence before
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
