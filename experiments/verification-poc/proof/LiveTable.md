# Live-clause table refinement

`LiveTable.lean` models zero-based entries containing a literal-pool range and a
live bit. Its database projection uses one-based clause IDs and hides dead
entries, including their retained metadata.

Nine reported theorems establish initial lookup and its connection to
`initialDatabase` under per-index range decoding; checked-range publication as
functional `insert`; clearing as functional `erase`; preserved deletion metadata;
unaffected slots; repeated clearing; and composition with the logical add/delete
calculus. The addition theorem requires an actual RUP derivation. Publishing an
arbitrary clause is not asserted to be sound.

`self_hosted_table_test.go` is a Go harness. It inserts read-only observations into
test-generated copies of the actual Oak stream checker after initialization and
every attempted command. Each snapshot compares all 256 entries (start, count,
live), the last addition ID, persistent refutation flag, and validity flag. Failed
deletions expose their partially updated table. Failed additions must not publish.
No production Oak source or language syntax is changed.

The oracle keeps a Go map of logical clauses, translates live IDs for the existing
Go RUP checker, and uses wide sums for range validation. `LiveTableCompare.lean`
independently executes the same layouts with Lean's proof-producing RUP checker
and compares the complete traces. The corpus reuses all 631 raw range layouts,
including sparse IDs, deleted hints, duplicate deletions, invalid suffixes,
resource boundaries, and malformed descriptors. Seven damaged expected traces
exercise the observer itself. Native cases retain the existing compilation and
execution limits and compile in batches of at most 64.

## Boundary

The table update equations and their logical step composition are proved in Lean.
The bounded trace executor and compiled Oak agree only on the tested corpus;
whole-run refinement, concrete array semantics, propagation scratch storage,
complete text grammar, and compiler correctness remain unproved. The observation
adapter, Go oracle, compiler, generated C, and C runtime remain trusted test
infrastructure. CI runs with warnings as errors and records axiom reports.

Next: propagation scratch-state refinement, beginning with encoded assignment
updates and conflict detection.
