# Native JSON codec comparison

This harness compares Oak's derived decoder with simdjson On-Demand for a
single explicit schema: `id: u64`, `active: Bool`, `samples: [4]i32`.
Both paths materialize all fields into the same C-compatible output shape,
require every field, reject duplicate/unknown fields, check integer ranges
and array lengths, and reject trailing content. Acceptance and exact decoded
values are checked before timing; each timed sample verifies a consumed
checksum. This is a narrow typed workload, not a general JSON speed ranking.

Requirements: Python 3, Go (the version in go.mod), C99 and C++17 compilers,
and a local simdjson checkout. CI pins simdjson to the revision in
`.github/workflows/json-benchmark.yml`; the harness records the actual SHA.
No dependency is downloaded by the harness. On an Apple M-series Mac:

```sh
python3 benchmarks/json/run.py --simdjson /path/to/simdjson --output results/m-series.json
```

Use a larger resident corpus to explore working-set sensitivity:

```sh
python3 benchmarks/json/run.py --simdjson /path/to/simdjson --documents 262144 --rounds 2 --samples 5 --output results/large-corpus.json
```

Documents are generated before measurement, padded for simdjson, and reused
by both implementations. Oak receives the logical length and retains bounded
reads; it does not use the padding as a license to overread. Corpus generation,
parser allocation, validation preflight, compilation, and output formatting
are outside timed regions. Timed work includes decoding, copying to the common
output structure, success checks, and the same checksum calculation. The C
bridge and simdjson decoder are separate/non-inlined calls; LTO is not enabled.
This measures the current Oak value ABI, including its aggregate copies.

Samples alternate backend order. Results contain raw durations, document/byte
counts, checksums, medians, revisions, compiler versions/flags, host details,
and the selected simdjson implementation. No allocations or hardware counters
are instrumented; allocation counts are explicitly unknown. Core affinity,
frequency, thermal state, and caches are not controlled. Large-corpus runs
are still repeated resident-memory traversal, not disk/network throughput or
guaranteed cold-cache measurements. Record external machine controls alongside
results when publishing. Do not compare sanitizer timing with release timing.

CI runs sanitizer checks and paired release measurements on Linux and ARM64
macOS. Each job compares the workflow's pinned baseline with the candidate
using 1,024 documents, 1,000 rounds and five samples per backend. The two
revisions run in separate processes, baseline first, on the same runner.
`compare.py` checks metadata compatibility and reports simdjson timing drift.
These hosted measurements are not a performance gate. Results and limitations
are recorded in [RESULTS.md](RESULTS.md). No parity
claim should be made from this harness alone: additional schemas, long strings,
floats, large arrays, and selective extraction need separate workloads.

The API and reuse choices follow simdjson's
[basics](https://github.com/simdjson/simdjson/blob/v4.6.11/doc/basics.md) and
[performance guidance](https://github.com/simdjson/simdjson/blob/v4.6.11/doc/performance.md).

Use `--inspect results/native` to retain the generated `schema.c` and
optimized `oak.s`. Assembly is produced with the same C flags as the timed
Oak object. Selected scanner/reader functions are also printed for inspection
in remote CI logs. The workflow uploads these files alongside raw JSON samples.
