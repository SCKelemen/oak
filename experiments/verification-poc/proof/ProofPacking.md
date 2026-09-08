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
