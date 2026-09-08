# Scanner state refinement

`ScannerState.lean` models the byte scanner used by Oak's isolated text proof
checker. It imports the bounded decimal arithmetic proofs and adds a relation
for partial numeric scans and invariants for the externally visible token state.
No production compiler or language syntax changes are required.

`Trace` specifies numeric scanning using ASCII classification and unbounded
arithmetic followed by a magnitude check. Each successful transition consumes
one byte and multiplies the previous value by ten before adding the digit.
Rejection consumes the first offending byte, preserves the previous magnitude,
and ignores the remaining suffix. Completion consumes the entire digit sequence.
`walk_trace` proves that the executable threshold-based model satisfies this
relation for arbitrary input lists and initial accumulators. `trace_bounds` and
`walk_bounds` prove cursor bounds, bounded partial magnitudes, and complete
consumption for successful scans, assuming a bounded initial accumulator.

The token model skips horizontal ASCII whitespace, distinguishes line feeds
from words and EOF, finds the complete word before numeric scanning, and retains
the sign distinction for negative zero. A nonnumeric word therefore advances the
outer cursor to its end even when the numeric scan stops early. EOF and line
feeds reset magnitude and sign to zero and one respectively.

`countWhile_bounds`, `scanTail_range`, and `scan_range` prove that token starts
and ends remain ordered and in bounds, that the next cursor equals the token
end, and that every non-EOF token advances the initial cursor. `scan_no_wrap`
proves that the resulting cursor fits in u32 for inputs at most 65,536 bytes.
Initial cursors must be within the input. `advance_refines` connects the local
threshold guard with the relational specification's mathematical arithmetic.

## Correspondence gate

The Go harness calls the actual `rup_token` through the ordinary Oak frontend
and compiled C. It checks kind and all five state slots after every call,
including repeated calls on the same state and poisoned initial output fields.
The independent Go oracle uses uint64 arithmetic followed by a magnitude check;
hand-labelled examples pin partial values, sign-only tokens, newline, EOF, and
negative zero. Byte arrays preserve every byte value in the shared JSON corpus.

The corpus covers every starting offset in representative streams, all 256
byte values, decimal threshold examples, 300 deterministic random streams,
repeated EOF, and 65,536-byte boundaries. `ScannerStateCompare.lean` checks the
same complete state sequences against the executable Lean model. Compiler
failures, traps, timeouts, missing tools, and malformed corpus data fail the gate.
The opt-in workflow retains the corpus, proof axiom reports, and comparison logs.

## Proof boundary

The numeric model-to-relation refinement and scanner cursor/range invariants
are proved in Lean. The compiled Oak-to-model correspondence is tested, not
universally proved. The range theorems do not establish a complete lexical
specification, the parser's clause-buffer invariants, or end-to-end DIMACS/LRAT
semantic preservation. The host harness, compiler, and execution environment
remain outside the proof. There is no claim that Oak or this system is fully
self-verified.

The next step is to connect scanner tokens to the decoder's clause and hint
buffer transitions, with explicit invariants for initialized prefixes and
zero terminators.
