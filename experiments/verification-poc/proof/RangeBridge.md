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

## Remaining boundary

The bridge and its soundness theorem are Lean model results. Universal refinement
of Oak's array accesses, mutable live-clause table, propagation scratch state,
and compiler output remains unproved. The complete external file grammar and
JSON adapters are outside these theorems. This is not a claim of a self-verified
Oak compiler or universal Oak checker soundness.

Next: relate the mutable live-clause table and its add/delete transitions to the
functional database used by the proved checker.
