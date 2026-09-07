# Complete bounded proof streams in Oak

`self_hosted_stream.oak` adds a decoded proof-stream checker around the Oak RUP
propagation kernel. It checks clause insertion, deletion, increasing addition
IDs, and the persistence of an established refutation. Both files remain in the
removable verification experiment.

## State and input contract

`RUPCommand` is an Oak record with an `addition: Bool` discriminator, a clause ID
or deletion stamp, a literal-pool range for an addition, and a reference-pool
range for hints or deletion IDs. True selects addition; false selects deletion.
The Boolean discriminator fits the current C backend’s primitive record layout.
These are decoded commands; there is no text parser or arbitrary action integer
in the Oak API.

The input literal pool uses the existing kernel's `2*variable + polarity`
encoding, with zero-based variables and polarity one for positive literals.
Clause IDs and references are one-based. Initial clauses receive IDs 1 through
N in order. Initial ranges, command records, and both pools are read-only.

The fixed profile permits:

| Resource | Limit |
| --- | --- |
| Variables | 1 through 64 |
| Initial clauses and maximum addition ID | 256 |
| Commands | 256 |
| Literal pool | 4,096 entries |
| Reference pool | 4,096 entries |
| Hints on one addition | 256 |

All mutable state is local stack storage: range tables, live flags, a remapped
hint buffer, proposed-clause scratch, and assignments. The input pools remain
unchanged on success and rejection. The checker publishes an addition's range
only after the RUP kernel accepts it. No heap allocation is used; the execution
test rejects allocation calls and unsupported-operation markers in generated C.

Range checks use `start <= size` followed by `count <= size - start` before
indexing or copying. All literals in the supplied pool are validated, including
unused entries and literals following a contradictory target prefix. This is a
strict decoded-input contract, not a promise to accept every storage layout that
happens to encode a semantically sound proof.

## Full-stream behavior

Every addition must have a fresh ID greater than the last addition ID. Hints
must name live clauses before propagation begins, including for tautological
targets. Deleted IDs cannot be reused for additions. Sparse increasing IDs are
allowed within the profile.

Deletions require a stamp at least as large as the last addition ID and check
references sequentially. Missing IDs, zero IDs, and repeated deletion IDs reject
the stream. A deletion stamp does not advance the last addition ID, matching the
Go and Lean checkers.

An initial or derived empty clause sets a persistent `refuted` flag. Deleting it
does not remove the fact that a contradiction was established. Processing still
continues to the end: any invalid suffix rejects the entire stream. Acceptance
requires both a valid complete stream and an established empty clause.

## Validation

From the experiment directory:

```sh
go test -count=1 -v . -run '^TestSelfHostedProofStreams$'
```

The test compiles the combined Oak source through the normal compiler, compiles
the generated C with the system C compiler, and executes a native binary. Missing
C tooling, compilation failures, timeouts, abnormal termination, and assertion
failures cannot count as a rejected proof.

The deterministic corpus includes 25 hand-labelled cases, 200 mutations of
valid streams, and 200 seeded generated streams. The Go ASCII LRAT checker reads
serialized versions of every stream; an independent exhaustive truth table
checks that its accepted initial databases are unsatisfiable. Oak executes the
same commands. CI saves a canonical JSON corpus and runs the existing Lean
`RUPCompare.lean` adapter over it using the proved `checkProof` implementation.

The hand-labelled cases cover derived and initial empty clauses, deletion after
refutation, valid and invalid suffixes, reused IDs, deleted and future hints,
duplicate and invalid deletions, sparse IDs, duplicate literals, deletion stamps,
and a multi-step proof that uses derived clauses after deleting earlier clauses.
Separate raw-layout tests require rejection of malformed offsets and counts,
invalid literals, out-of-range references, and resource-limit violations. These
are distinguished from semantic parity because the bounded Oak profile may
reject inputs outside its capacity that the unbounded Lean checker accepts.

[The three-way comparison passed](https://github.com/SCKelemen/oak/actions/runs/34166818760):
104 accepted and 321 rejected decisions agree across all 425 streams, and all 11
malformed/resource cases reject in Oak. The earlier 400-case Oak RUP-step corpus
and the existing Go/Lean decoded, text, and Boolean CNF comparisons also passed.
`../validation-self-hosted-stream.json` records the tested code commit and the
execution and proof boundaries.

## Remaining proof boundary

The Oak implementation is tested against the proved Lean reference. Agreement
on this corpus does not establish refinement for all possible Oak executions.
The trusted execution path still includes Oak's compiler and generated C, the C
compiler/runtime, and the Go harness. No new formal theorem is claimed for the
Oak implementation itself.

ASCII DIMACS/LRAT parsing, source-to-CNF correspondence, and evidence receipts
remain in Go or Lean. The existing solver certificate gates still use those
implementations. This milestone does not route arbitrary solver files into Oak
or claim that the toolchain is self-verified. RAT, binary LRAT, extension
variables, and theory lemmas remain unsupported.

The next self-hosting boundary is a bounded ASCII decoder that feeds this stream
checker, followed by differential replay of real solver certificates within the
supported resource profile.
