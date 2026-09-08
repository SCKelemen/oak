# Completed ranges and proof-stream semantics

`RangeBridge.lean` connects flat pools and start/count descriptors to the proved
decoded RUP/deletion checker. It imports the packed-buffer invariants and
`RUPExecutable.lean`; no production Oak or compiler changes are required.

## Meaning of stored data

`decode_encode` proves that encoding a positive-index logical literal and then
decoding it preserves its index and polarity. `encode_decode` proves the reverse
round trip for every encoded natural number. `decoded_bounds` connects Oak's
encoded-variable guard to the one-based variable bounds of the logical checker.

`readRange_refines` relates the subtraction-based range guard to mathematical
start-plus-count bounds. `range_contents` proves that a range selects exactly
its items from a pool with arbitrary preceding and subsequent data. This covers
closed ranges after later appends, including empty ranges. `completed_pending`
connects that fact to `Packed.closeSegment` and its initialized-prefix invariant.
`clause_contents` maps exactly the selected literals into logical clauses;
`reference_contents` preserves reference IDs, their order, and duplicates.

## Executable bridge and soundness

The executable range decoder checks the bounded representation profile and
constructs initial clauses and decoded additions/deletions. Literal ranges on
deletions are ignored, as in Oak. Every literal pool element is validated, even
if unused; reference IDs are validated only when selected. The decoded checker
then enforces liveness, ID progression, RUP justification, and valid suffixes
after a refutation.

`checkLayout_sound` proves that acceptance implies an unsatisfiable initial
database reconstructed by this range decoder. It composes with
`checkProof_sound` and does not assume an Oak-to-model correspondence theorem.
The round-trip and range-content theorems establish the representation meaning
of the reconstructed clauses and reference lists.

## Native comparison

The Go harness calls the actual, uninstrumented `rup_stream_check` through the
ordinary Oak frontend and generated C. It exports raw pools and descriptors,
the expected decoded clauses/commands, and the final checker decision. Lean
compares both decoded meaning and acceptance against that corpus. The native
Oak comparison checks acceptance; it does not observe Oak's internal decoded
logical values. Go uses a wide-sum range guard and its existing LRAT checker.
Accepted cases are independently checked against their initial truth tables,
or an explicit initial empty clause.

Coverage includes the existing stream corpus, successful layouts from the
packed-buffer corpus, all 128 literal encodings in the supported variable range,
overlapping/reordered ranges, empty end ranges, invalid offsets and counts,
unused pool data, ignored deletion literal fields, pool limits, hint limits,
and deletion-stamp limits. Crashes, timeouts, and compilation errors fail the
test. The existing text and actual-certificate gates remain in place.

The growing native corpora are compiled in batches of at most 64 independent
cases. This avoids repeated source-position conversion across one enormous
translation unit. Each case body and assertion is preserved; the splitter rejects
missing, duplicated, reordered, or additional main assertions. Coverage tests
check that every case appears exactly once across batches. Per-compilation and
native-execution time limits are unchanged. Batching affects only the Go test
harness; no compiler optimization or checker behavior change is required.

[The soundness gate passed](https://github.com/SCKelemen/oak/actions/runs/34222134683/job/102047501554):
all nine reported theorems were checked without proof holes or project-specific
axioms. All 631 layouts agreed on acceptance (244 accepted, 387 rejected).
Go and Lean also agreed on representation decoding and on the complete meaning
of all 522 decodable layouts. Of the rejected layouts, 109 fail representation
guards and 278 decode but fail proof checking. The axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`; the canonical corpus and logs are
retained with the CI artifact. `../validation-range-bridge.json` records the
tested commit and exact scope.

The complete native suite and batching coverage tests passed with Go's race
detector. The range comparison took 10.94 seconds and the scanner corpus 29.37
seconds in that run. External solver and certificate gates passed, including
11 accepted Lean certificate checks with 22 rejected corruptions and one
accepted Oak ASCII replay with two rejected corruptions. Boolean proof and
invariant-model gates passed as well.

Repository CI and the standard-library suite also passed after batching, as did
formal-verification and golden-file checks. No package or subprocess timeout
limits were increased, and no corpus cases or assertions were removed.

## Remaining boundary

The bridge and its soundness theorem are Lean model results. Universal refinement
of Oak's array accesses, mutable live-clause table, propagation scratch state,
and compiler output remains unproved. The complete external file grammar and
JSON adapters are outside these theorems. This is not a claim of a self-verified
Oak compiler or universal Oak checker soundness.

The [live-table milestone](LiveTable.md) now proves the model's publication and
deletion equations against the functional database and compares complete native
table snapshots. Whole-run and concrete array refinement remain open.
