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
invariant, and a sequence theorem covers successful reads in a fixed mode.
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

## Validation

[The soundness job passed](https://github.com/SCKelemen/oak/actions/runs/34284667952/job/102257356593)
on commit `24585b30e72269e4829d5a747c0c78e3c9ca225d`. All 12 theorem audits
passed with warnings treated as errors, without proof holes or project-specific
axioms. Dependencies are limited to standard `propext`, `Quot.sound`, and
`Classical.choice`.

The publication-state adapter, earlier buffer adapter, Go oracle, and compiled
Oak agreed on all 72 cases: 52 decoded layouts and 20 rejected inputs. Native
buffer comparison took 3.32 seconds without the race detector. Existing proved
packing comparisons passed 425 cases, and certified streams passed 887 layouts
(308 accepted, 579 rejected; native comparison 55.95 seconds).

[The solver job passed](https://github.com/SCKelemen/oak/actions/runs/34284667952/job/102257356714).
The buffer corpus also passed with the race detector in 5.41 seconds. Existing
real-certificate replay accepted nine bounded certificates and rejected 18
corruptions, with two certificates explicitly outside the bounded profile.
All 11 source certificates and 22 corruptions passed the earlier Lean text gate.
Boolean proof/model checks and the full external solver suite passed.
These certificate gates retain the previously proved packing/text entry path;
they do not yet use a complete file parser assembled from publication states.

Repository CI, standard-library race tests, Oak testing tools, formal verification,
golden files, and AArch64 memory refinement all passed on the tested commit.
`../validation-segment-publication.json` records the exact scope and job links.

Next: prove command assembly from published clause and hint ranges, including
addition IDs and deletion stamps, before connecting the complete file state machine.
