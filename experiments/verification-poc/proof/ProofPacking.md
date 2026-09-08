# Proved packing of decoded proof streams

`ProofPacking.lean` packs decoded clauses and instructions into literal and hint
buffers. It preserves clause order, duplicate literals, addition IDs, deletion
stamps, and hint order. Initial clauses and additions use offsets into the
concatenated literal pool; deletions allocate only reference slots.

The range lemmas quantify over arbitrary preceding and following buffer contents.
The round-trip theorem states that decoding any supported packed input returns
exactly its original clauses and instructions. Supported inputs have positive
literal indices, bounded references and command metadata, and the existing range
decoder's resource and variable-domain conditions. Proof validity, liveness, and
unsatisfiability are not assumed by the round-trip theorem.

`ProofPacking.check` executes those support checks and the certified stream.
Its soundness theorem concludes unsatisfiability of the supplied clause database
from acceptance alone. This connects packing, executable range decoding, and
certified propagation without a supplied representation equation or a runtime
comparison against the original decoded input.

The certificate replay gate uses this packer and retains the previous imperative
packer as an independent reference. Full raw-layout equality and decoded-content
equality remain mandatory regression checks. Supported real certificates must
also pass the new composed checker. The existing Go harness replays all emitted
layouts in compiled Oak. The existing 425 decoded stream cases additionally
compare the new packing composition with Oak, Go, and both Lean streams.

## Boundary

This proves packing of decoded data, not correctness of the external DIMACS/LRAT
grammar or universal refinement of Oak's concrete text parser. The existing Lean
text parser supplies the decoded data in the replay gate. JSON adapters, the Go
harness, and Oak/compiler/C-runtime correspondence remain tested infrastructure.
No Python or production language changes are introduced.

`PackedText.check` composes the existing executable text parsers with the proved
packing checker. Its acceptance theorem supplies the actual parser results and
unsatisfiability of that parsed initial formula. Real certificates and both
corruptions must also pass this text-entry comparison. This theorem concerns the
parser's returned data; it does not establish external grammar conformance.

## Validation

[The soundness job passed](https://github.com/SCKelemen/oak/actions/runs/34282323768/job/102249772228)
on commit `bb8932260e444d56f2d009fdefcde16ddbdcd0e4`. Eight theorem reports
and two executable-definition reports passed with warnings treated as errors,
without proof holes or project-specific axioms. Dependencies are limited to
standard `propext`, `Quot.sound`, and `Classical.choice`.

The new packing comparison agreed on 425 streams: 104 accepted and 321 rejected.
The existing raw-stream comparison also passed all 887 layouts: 308 accepted
and 579 rejected. Its native run took 44.98 seconds without the race detector.

The solver installer initially rejected TLC's mutable prerelease asset because
its checksum had changed. The pin was explicitly refreshed to GitHub's published
SHA-256 `4c7bb1f6b050d56c197ee9ddd6e57fe521eae175f5043c9fb98b169f7b2d5407`
for release asset `551007111`, updated on 2026-09-08. The lock records that asset,
the release tag commit, and the digest source. Download checksum enforcement
remains mandatory; no automatic acceptance of future artifact changes was added.

[The solver job passed](https://github.com/SCKelemen/oak/actions/runs/34282323768/job/102249771902).
Nine actual certificates passed the proved packing checker and text-entry checker;
18 corruptions were rejected. All nine layouts matched the imperative reference
exactly. Compiled Oak and Go replayed all 27 emitted layouts in 2.13 seconds.
Two certificates were explicitly outside the fixed profile. The existing Lean
text gate still accepted all 11 source certificates and rejected 22 corruptions.
The raw 887-layout suite passed with the race detector in 86.85 seconds. Existing
Boolean proof and model gates passed, as did the refreshed TLC download checksum
and the external solver suite.

Repository CI, standard-library race tests, Oak testing tools, formal verification,
golden files, and AArch64 memory refinement all passed on the tested commit.
`../validation-proof-packing.json` records the precise scope and job links.

Next: connect the Oak text-decoder state model to this proved packer, beginning
with publication of completed clause and hint segments into the same ranges.
