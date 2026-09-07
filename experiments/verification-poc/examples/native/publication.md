# Bounded release/acquire publication

`publication.json` checks the publication chain from Oak's memory model:

1. Thread 0 writes an ordinary payload at location 1.
2. Thread 0 release-writes a flag at location 2.
3. Thread 1 acquire-reads **that specific flag write**.

The claim is that the payload write happens-before the flag observation. A
subsequent ordinary payload read in thread 1 is therefore ordered after the
payload write and does not race with it. No payload value is modeled.

The model has four Boolean fields and 16 admissible bit states. Four states are
reachable: empty prefix, payload written, flag published, flag observed.
`ordered` records the HB edge from event 0 to event 2. The invariant includes
protocol consistency (`published → written`, `observed → published`) and
`ordered = observed`. This strengthening is inductive and includes the desired
publication property.

`publication-relaxed.json` changes the observation rule so it creates no HB
edge. Its four-state counterexample ends when the flag is observed without
publication ordering. It demonstrates failure of this publication proof,
not a particular payload value in an execution containing a data race.

`publication_test.go` compares every reachable prefix with the actual
`semir.MemoryExecution` API. It covers release/acquire, release/relaxed,
relaxed/acquire, and relaxed/relaxed flags, and extends observed prefixes with
a payload read to check the race corollary. It also rejects fabricated SW
edges lacking the correct reads-from or acquire witness.

This is a bounded correspondence test: two threads, two locations, one payload
write, one flag write, and one observation of that write. Initial flag reads,
repeated publication, other writes, fences, release sequences, thread lifetime,
fairness, liveness, and backend/compiler refinement are outside the model.
A source-level concurrent Oak program is not being verified automatically.

```sh
go run . prove-local --out build/publication.proof.json examples/native/publication.json
go run . trace --out build/publication.trace.json examples/native/publication-relaxed.json
go test -run 'TestPublication' -v .
```

Both projects are also part of the external solver suite.
