# Legacy borrow-checker harnesses

These scenario files were historically named `borrowchecker_test_*.go`, which means Go
compiled them into the production package rather than executing them as tests. When
activated as `*_test.go`, much of their embedded source targets superseded Oak syntax
and older diagnostic wording.

They are retained as language-migration input, not normative current tests. Current
borrow semantics are covered by ordinary `*_test.go` files next to the checker; useful
cases should be ported individually to canonical Oak syntax and stable diagnostic codes.

`borrowchecker_test_helper.go` was different: current executable tests depend on its
setup helper, so it is retained as the real test-only file `test_helper_test.go`.

During this reconciliation, the formal half-open region model exposed a real bug in the
runtime checker: a zero-length region located inside a non-empty region was incorrectly
classified as overlapping. The current `region_overlap_test.go` now exercises the region
algorithm directly, including empty, adjacent, overlapping, unknown, and symmetric cases,
so this invariant is no longer dependent on legacy source fixtures.
