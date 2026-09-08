# Publishing decoded segments

`SegmentPublication.lean` connects the existing byte-reading buffer decoder to
`ProofPacking.segments`, the range layout used by the proved packer. It reasons
about the actual executable `Packed.segmentLoop`, including scanner advancement,
newlines, numeric tokens, capacity failures, zero termination, and the special
spelling rule for deletion terminators.

Every successful segment read appends a suffix to the pool, closes exactly one
segment, clears pending data, and preserves capacity. The completion theorem
also handles an entry buffer with pending data; publication uses the stronger
invariant that pending data is empty between segments.

The executable publication state records each completed segment's start and
count. Its invariant states that the full metadata sequence is exactly
`ProofPacking.segments 0 buffer.closed`. Successful publication preserves that
invariant, and the theorem extends to any successful sequence of segment reads.
Each published range returns precisely its segment's encoded values, even after
arbitrary later buffer appends. The corresponding clause range decodes those
values through the existing literal decoder.

`SegmentPublicationCompare.lean` uses this state for initial clauses, added
clauses, hints, and deletion references. It reads stored publication metadata to
construct the complete layout and compares it to the existing Go oracle and
compiled Oak observations. The existing 72-case buffer corpus includes empty
segments, signed zero, deletion spelling, malformed input, and capacity limits.
The Go harness and native Oak implementation are unchanged.

## Boundary

The proved connection is from the executable Lean model of Oak's segment decoder
to the proved packer's range layout. Universal refinement of the compiled Oak
implementation remains open. Full DIMACS/LRAT file parsing, command-ID scheduling,
and complete text-to-stream state composition are not established here. Rejected
reads return no publication state; exact partial native mutations on failure are
outside these acceptance and publication theorems.
