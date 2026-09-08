# Clause and hint buffer invariants

`PackedBuffers.lean` models a flat initialized pool, its closed segments, and
its pending segment. `WellFormed` requires the pool to equal the concatenation
of the closed segments followed by the pending segment, within capacity.

An accepted `push` preserves every initialized item and every closed segment,
appends exactly one item, and writes below capacity. `seal` leaves the pool
unchanged, records the pending segment (including an empty segment), and clears
the pending segment. Its start/count pair covers exactly the pending suffix;
every offset below that count is in bounds. Thus a zero terminator consumes no
pool slot, even when the pool is full.

`tokenStep` classifies scanner tokens as literals, hints, or deletion references.
Nonzero literals are encoded after checking their variable bound; nonzero
references require a positive sign. Zero closes the segment. Deletion's exact
single-byte `0` spelling is enforced in the byte adapter. `tokens_preserve` and
`segmentLoop_preserves` connect successful token sequences and byte scanning to
the initialized-prefix invariant. The latter uses the executable scanner from
the preceding milestone. Theorems are checked with warnings treated as errors;
the public proof assumptions are printed in CI.

## Actual decoder comparison

The Go harness instruments only the decoder's entry signature and final handoff
to `rup_stream_check`. All scanning, appending, range construction, and parser
control flow remain the actual Oak implementation. An observer checks the full
literal pool, initial-clause starts and sizes, reference pool, and every command
field. Separate result codes distinguish decoder rejection, a layout mismatch,
and an exact match. Failure to find the exact observation seam fails the test.
The production experiment files are unchanged by this instrumentation.

The oracle uses Go integer parsing and list construction. A shared JSON corpus
is replayed by Lean using the scanner and packed-buffer model. It covers empty
segments, signed zero, literal encoding, negative/overflowing references,
malformed and missing terminators, deletion spelling, 4,096-item boundaries,
capacity shared across initial clauses and additions or hints and deletions,
256-clause/command boundaries, and deterministic generated layouts. Periodic
array initialization keeps large boundary inputs small in the generated code.

Decoding a layout is not acceptance of a proof. The observer deliberately
replaces the proof check so that invalid references and non-refuting layouts
can still exercise buffer construction. Existing uninstrumented checker and
real-certificate gates continue to run separately.

## Remaining boundary

The initialized-prefix and range invariants are universal Lean model theorems.
Concrete Oak arrays, rejected executions' intermediate state, full file grammar,
command-ID policy, and the compiler remain outside those proofs. The byte adapter
checks one segment, not the entire DIMACS/LRAT grammar; the layout adapter and JSON
transport are test infrastructure. Agreement with compiled Oak remains tested.

Next: relate completed clause and command ranges to the decoded proof-stream
checker, preserving the meaning of each stored literal and reference.
