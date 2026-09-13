# Rings benchmarks

This harness times the rings of `stdlib/rings.oak` (docs/spec/65-machine-memory.md
§1; the `rings` package of `stdlib/README.md`) between threads, compiled
through the C backend and driven by pthreads, against Go's buffered channels
carrying the same items between the same thread shapes. It exists to give
each ring a cost the storage engine can plan with; it is not a ranking.

Requirements: Python 3, Go (the version in `go.mod`), and a C11 compiler
with pthreads. On this repository's root:

```sh
python3 benchmarks/rings/run.py --output benchmarks/rings/local.json
```

`--items` sets the items each transfer moves (two million by default),
`--samples` the timed runs (five; medians are reported), `--skip-go` times
Oak alone, `--inspect DIR` keeps the generated C.

## What is measured

One transfer per ring: the producers push a fixed sequence, the consumers
pop until every item arrived, and the wall time of the whole transfer —
thread start to last join — divided by the item count is the cost per
item. Every run verifies the checksum of what arrived before it counts. The
Oak side is `benchmarks/rings/oak/main.oak` (the loops the correctness
harness `compiler/e2e_rings_test.go` runs, over storage `bench.c` owns);
the capacity is 1024 slots; a producer that finds the ring full spins, and
the spins are recorded. The Go reference moves the same items through a
`chan uint32` of capacity 1024.

| Ring | Threads | What it exercises |
| --- | --- | --- |
| `spsc` | 1 producer, 1 consumer | release/acquire handoff with cached indices on separate cache lines |
| `mpsc` | 4 producers, 1 consumer | compare-exchange claims on `tail`, per-slot sequence cells |
| `mpmc` | 4 producers, 4 consumers | compare-exchange claims on both counters |
| `intrusive` | 4 producers, 1 consumer | one exchange and one release per push over preallocated nodes |

Results are in [RESULTS.md](RESULTS.md); raw data beside it.
