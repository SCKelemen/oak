# Certified live-table proof streams

`CertifiedStream.lean` connects the certified propagation chain to the live range
table. Each state carries model preservation from the initial database and a
persistent refutation certificate. Additions publish a range only after the new
chain returns a clause-entailment certificate. The proved table equations turn
publication into logical insertion and clearing into logical deletion.

A derived empty clause certifies unsatisfiability of the initial database. Deleting
it preserves that certificate. Deletion stamps leave the last addition ID unchanged;
missing and duplicate deletions reject sequentially. Fresh IDs, live hints, range
bounds, and the existing resource profile are checked. Every command in the suffix
must succeed, even when an earlier command has already established refutation.

`check_sound` proves that acceptance implies unsatisfiability of the initial range
table's logical projection. `decoded_sound` transports that result to
`initialDatabase clauses` under the explicit per-index range-decoding equation.
There is no semantic premise asserting that the initial database is unsatisfiable.
Five theorem reports and seven executable-definition reports audit initialization,
certified publication, clearing, sequential deletion, command processing, and
whole-stream checking. Executable state proof fields erase at runtime.

The Go harness calls unmodified Oak `rup_stream_check`. Its 887 layouts include
all 631 preceding raw-range cases plus 256 constructed cases over 1..64-variable
chains. These repeatedly publish units and delete their predecessor, derive and
delete an empty clause, and continue with a valid tautology. Three mutations reject
ID reuse, hints to the deleted empty clause, and duplicate deletions after
refutation. The new Lean stream and the original Lean range/stream checker must
both agree with the Go oracle and compiled Oak.

## Boundary

Whole-stream soundness of this new Lean model is proved. Universal equivalence
with the concrete Oak executor or the original Lean checker is not proved; that
correspondence is tested on the corpus. The original `decoded_sound` theorem retains a representation premise;
[`InitialDecoder.lean`](InitialDecoder.md) now derives it from successful
executable range decoding. A failed
deletion returns no certified state; the exact partial mutation on rejected inputs
is covered by the preceding native table-trace tests, not this acceptance theorem.

The checker remains an isolated alternative. Production Oak, the original stream
path, and the existing external certificate gates are unchanged. JSON adapters,
the Go harness, Oak compiler, generated C, and C compiler/runtime remain trusted
test infrastructure. Full text-grammar and compiler refinement remain open.

The subsequent [initial-decoder milestone](InitialDecoder.md) adds real-certificate
replay and removes the supplied per-index equation from the composed theorem.

## Validation

[The soundness gate passed](https://github.com/SCKelemen/oak/actions/runs/34238014168/job/102100656518)
on commit `ff79a91ca19a37d75d7601d3bf9a52d1668d45a9`. All five theorem reports
and seven executable-definition reports passed with warnings as errors, without
proof holes or project-specific axioms. The reports use only standard `propext`,
`Quot.sound`, and `Classical.choice`.

Oak, Go, the new certified stream, and the original Lean stream agreed on all
887 layouts: 308 accepted and 579 rejected. All 256 constructed publish/delete
and suffix cases behaved as expected. Native comparison took 43.82 seconds
without the race detector. The canonical corpus and proof/comparison logs are
retained for 30 days; `../validation-certified-stream.json` records the exact
scope and tested commit.

The native comparison also passed with Go's race detector in 72.79 seconds. The
full native suite and existing external/certificate gates passed, including
11 accepted Lean certificates and 22 rejected corruptions, the Boolean proof
bridge, and the invariant-model gate. At that milestone these certificate gates used
the original stream path. The subsequent [decoder milestone](InitialDecoder.md)
adds direct real-certificate replay through the certified stream.

Repository CI, standard-library, formal-verification, golden-file, and AArch64
memory-refinement checks all passed on the tested commit. Existing gates, corpus
coverage, and timeout limits were preserved.
