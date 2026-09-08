# Certified live-table proof streams

`CertifiedStream.lean` connects the certified propagation chain to the live range
table. Each state carries model preservation from the initial database and a
persistent refutation certificate. Additions publish a range only after the new
chain returns a clause-entailment certificate. The proved table equations turn
publication into logical insertion and clearing into logical deletion.

A derived empty clause certifies unsatisfiability of the initial database. Deleting
it preserves that certificate. Deletion stamps leave the last addition ID unchanged;
missing and duplicate deletions reject sequentially. Fresh IDs, live hints, range
bounds, and the existing resource profile are checked. Every command in the suffix
must succeed, even when an earlier command has already established refutation.

`check_sound` proves that acceptance implies unsatisfiability of the initial range
table's logical projection. `decoded_sound` transports that result to
`initialDatabase clauses` under the explicit per-index range-decoding equation.
There is no semantic premise asserting that the initial database is unsatisfiable.
Five theorem reports and seven executable-definition reports audit initialization,
certified publication, clearing, sequential deletion, command processing, and
whole-stream checking. Executable state proof fields erase at runtime.

The Go harness calls unmodified Oak `rup_stream_check`. Its 887 layouts include
all 631 preceding raw-range cases plus 256 constructed cases over 1..64-variable
chains. These repeatedly publish units and delete their predecessor, derive and
delete an empty clause, and continue with a valid tautology. Three mutations reject
ID reuse, hints to the deleted empty clause, and duplicate deletions after
refutation. The new Lean stream and the original Lean range/stream checker must
both agree with the Go oracle and compiled Oak.

## Boundary

Whole-stream soundness of this new Lean model is proved. Universal equivalence
with the concrete Oak executor or the original Lean checker is not proved; that
correspondence is tested on the corpus. Initialization uses the functional range
table, so the decoded-clause transport retains a representation premise. A failed
deletion returns no certified state; the exact partial mutation on rejected inputs
is covered by the preceding native table-trace tests, not this acceptance theorem.

The checker remains an isolated alternative. Production Oak, the original stream
path, and the existing external certificate gates are unchanged. JSON adapters,
the Go harness, Oak compiler, generated C, and C compiler/runtime remain trusted
test infrastructure. Full text-grammar and compiler refinement remain open.

Next: replay real certificates through the new certified stream and connect the
text/range decoder to its initial-database representation without a supplied
per-index equation.
