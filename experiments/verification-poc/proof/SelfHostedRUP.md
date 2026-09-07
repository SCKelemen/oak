# First proof-checking kernel written in Oak

`self_hosted_rup.oak` is the first executable part of the certificate checker
implemented in Oak itself. It checks one decoded reverse unit propagation (RUP)
addition against a supplied clause database and ordered hint chain. The file is
inside the removable verification experiment and introduces no language syntax
or production compiler hook.

The kernel uses caller-owned arrays and views for clauses, offsets, lengths,
the proposed clause, hints, and assignment scratch. It performs no allocation.
The CI test compiles the source with Oak's normal compiler, compiles the emitted
C, and runs the native result. Generated C is rejected if it contains an
allocation call or an unsupported-operation marker.

## Compact interface

Literals use `2*variable + polarity`, where variables start at zero and polarity
one means positive. Hint indices start at zero. The adapters translate these to
the one-based signed literals and one-based clause IDs used by DIMACS/LRAT.

The checker validates:

- nonempty variable domains of at most 64 variables and sufficient scratch;
- clause, target, hint, offset, and length bounds before indexing;
- every hint before accepting a target containing complementary literals;
- target assumptions and contradictory assumptions;
- rejection of a hinted clause already satisfied by propagation;
- set semantics for duplicate literals;
- exactly one unassigned literal for a unit step;
- a conflicting final hint, with no unused suffix.

An empty hint chain is rejected unless the target assumptions already conflict.
Every error returns `false`; the kernel has no parser, diagnostics, or proof
receipt format.

## Differential validation

`self_hosted_rup_test.go` generates a deterministic 400-case corpus. It obtains
the reference answer from the Go LRAT checker, emits calls to the Oak kernel,
compiles and runs them, and saves the canonical JSON corpus. The cases combine
empty and nonempty clauses, complementary and duplicate literals, empty and
ordered hint chains, invalid or future hints, unit propagation, satisfied hints,
non-unit hints, and conflicts before or at the end of a chain.

`SelfHostedRUPCompare.lean` decodes the same corpus and compares every decision
with the proved Lean `checkRUP`. CI observed 65 accepted and 335 rejected cases.
Lean's general `checkRUP_sound` theorem proves soundness for every input accepted
by the Lean checker. The finite comparison is strong regression evidence that
the Oak implementation follows it; it is not a proof of refinement for every
possible Oak execution.

## Current boundary

This kernel implements one decoded RUP addition. The subsequent
[stream checker](SelfHostedStream.md) now implements complete bounded decoded
addition/deletion streams, database updates, increasing IDs, and persistent
refutation in Oak. ASCII parsing, source-CNF reconstruction, and receipts still
run in Go or Lean. RAT, binary LRAT, extension variables, and theory lemmas
remain unsupported throughout this prototype.

The trusted path for the Oak result includes the Oak parser, typechecker, lowering,
generated C, C compiler, runtime, and the differential harness. We have not yet
proved that `self_hosted_rup.oak` refines Lean's checker, nor that the Oak compiler
preserves its semantics. Calling this kernel self-hosted means the checker logic
is authored and executed as Oak code; it does not mean Oak is self-verified.

The bounded proof-stream milestone builds on this kernel without changing its
API. The ASCII decoder can move across the boundary separately.

[The Oak, Go, and Lean comparison passed](https://github.com/SCKelemen/oak/actions/runs/34165110343):
65 accepted and 335 rejected decisions agreed across all three implementations.
The repository's CI, standard-library, formal, and golden-file workflows also
passed. `../validation-self-hosted-rup.json` records the tested commit, coverage,
execution trust, and remaining self-hosting boundary.
