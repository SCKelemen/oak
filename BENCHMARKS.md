# Oak benchmarks

The measured record of where Oak's generated code stands against the
implementations people actually use. Two harnesses exist, both checked in
with their raw samples; every number below is a median from a file in
`benchmarks/`, and no number is quoted here that cannot be regenerated from
one. Correctness is checked before timing in both: the JSON harness
verifies every decoded value and a consumed checksum, the kernel harness
refuses to record a timing until Oak, Go, and Rust agree on the result.

Read the caveats first. These are single machines, uncontrolled for
frequency, affinity, thermal state, and caches, with the run's own
metadata (compiler versions, flags, CPU, revision) in each results file.
A few percent of drift between runs is normal. Nothing here measures
allocation counts or hardware counters. The workloads are the ones named,
not a general ranking.

## Kernels against Go and Rust

`benchmarks/kernels` (`RESULTS.md`, `results/*.json`). Six kernels written
plainly in each language on identical data: CRC-32C, SHA-256, and BLAKE3
over 1 MiB, an f32 dot product and a u64 sum over 2^20 elements, and a
binary search of 2^16 probes in 2^20 sorted keys. Oak compiles through
`oak build` to C and `cc -O3` with every bounds check the checker cannot
prove left in; Go is `go build`; Rust is `rustc -O` with the standard
library only. The Go standard library rows use the CPU's SHA-256 and
CRC-32C instructions and are shown as the ceiling a portable-C backend does
not reach without intrinsics.

Apple M-series, macOS, 2026-09-11, nanoseconds per operation, medians of
seven interleaved samples of five rounds:

| Kernel | Oak | Rust | Go generic | Go stdlib | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: |
| crc32c | 2,386,600 | 2,170,400 | 2,554,883 | 119,850 (hardware) | 1.10× |
| sha256 | 2,632,400 | 2,732,350 | 3,383,175 | 371,183 (hardware) | 0.96× |
| blake3 | 1,911,200 | — | — | — | — |
| dot | 604,600 | 631,450 | 961,717 | | 0.96× |
| sum | 89,600 | 88,058 | 310,608 | | 1.02× |
| search | 7,478,000 | 7,499,675 | 11,266,700 | | 1.00× |

What moved these numbers: the same day's baseline had Oak at 4,424,600
on CRC-32C and 3,444,600 on SHA-256. The gap closed without intrinsics or
algorithmic tricks beyond a byte table, by adding four extent facts to the
checker (a literal loop bound, a scaled index, a lower bound with
subtraction, a masked index — each with its law in `Oak.Extents` and a
test of what stays checked) and rewriting the standard library's hashes to
sit under them, so every block and table access is proven and emitted
unchecked. That is the intended relationship between the proofs and the
performance: a check is removed only when the checker can show it never
fails, and the removal is where the speed comes from. A second run the
same day, after the facts learned to name record field paths
(`tail.block[tail.filled]` under `tail.filled < 64`), has CRC-32C at
2,009,800 against Rust's 2,022,842 and SHA-256 at 2,563,400 against
2,636,150; the hash package's remaining checked accesses fell from eight
to four, all four under a record invariant the extent facts cannot state.

### Workload shapes

Four more kernels shaped like the sibling projects' hot loops, with Go
and Rust twins of identical arithmetic (`benchmarks/kernels/RESULTS.md`,
`m-series-2026-09-11-shapes.json`, updated by `m-series-2026-09-12-popcount.json`):

| Kernel | Shape | Oak | Rust | Go | Oak / Rust |
| --- | --- | ---: | ---: | ---: | ---: |
| page_probe | B-tree leaf probe (dbs) | 7,913,200 | 7,735,183 | 11,041,675 | 1.02× |
| bitmap | allocator bitmap scan (os) | 150,600 (hardware popcount) | 139,758 (hardware popcount) | 346,675 (hardware) | 1.08× |
| dispatch | bytecode dispatch (os) | 6,902,600 | 7,070,558 | 6,953,242 | 0.98× |
| tiled | tiled f32 reduction (ml) | 131,400 | 156,750 | 329,317 | 0.84× |

Every access in `tiled`, `bitmap`, and `dispatch` is proven and emitted
unchecked; `page_probe` keeps two checked reads under a binary search's
decreasing bound, which the extent facts do not yet track. `bitmap` is
the population-count instruction in all three languages now that
`arm64.cnt64` exists (`docs/spec/92-ffi.md` §3.2); the numbers are from
`m-series-2026-09-12-popcount.json`, a later run of the same machine on
which every row moved together.

## Typed JSON decoding against simdjson

`benchmarks/json` (`RESULTS.md`, `*.json`). Oak's derived decoder for one
explicit schema (`id: u64`, `active: Bool`, `samples: [4]i32`) against
simdjson On-Demand, both fully materializing and validating every field,
timed per document over a resident corpus. Three optimization passes are
recorded with their paired baselines and workflow links; the latest:

| Runner | Oak ns/document | simdjson ns/document | Oak / simdjson |
| --- | ---: | ---: | ---: |
| Apple M1 (virtual, CI) | 119.91 | 105.87 | 1.13× |
| AMD EPYC 7763 (CI) | 178.67 | 127.58 | 1.40× |

This is a narrow typed workload, not a general JSON ranking; additional
schemas, long strings, floats, large arrays, and selective extraction need
their own workloads before any parity claim.

## What is not measured yet

Kernels shaped like the database's page and B-tree paths, the hypervisor's
dispatch and bitmap scans, and the ml runtime's tiled reductions; Rust's
`sha2`/`crc32c` crates (the harness is offline and uses the standard
library only); anything with allocation; anything on x86 for the kernels.
Each of these is a row to add to `benchmarks/kernels`, not a claim to
make in advance.

## Reproducing

```sh
python3 benchmarks/kernels/run.py --output results/kernels.json
python3 benchmarks/json/run.py --simdjson /path/to/simdjson --output results/json.json
```

Both drivers record the revision, compilers, flags, and host in their
output; publish those alongside any number.
