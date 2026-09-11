# Standard library benchmarks

This harness times Oak's standard-library packages, compiled through the C
backend, against the same workloads written with Go's standard library and,
where a reference is cheap and unambiguous, against plain C (libc `qsort`,
a LEB128 loop). It exists to find where Oak is slow and to keep the numbers
honest while that is fixed; it is not a ranking of languages.

Requirements: Python 3, Go (the version in `go.mod`), and a C99 compiler.
Nothing is downloaded. On this repository's root:

```sh
python3 benchmarks/stdlib/run.py --output results/local.json
```

`--scale` multiplies every corpus size (`1.0` is the documented size,
`0.02` is the CI sanitizer smoke), `--samples` sets the timed runs per
backend, `--only sort/` restricts to a workload prefix, `--cflags` replaces
the default `-O2`, `--sanitize` runs the Oak side under ASan/UBSan for
correctness only, `--skip-go` times Oak alone, and `--inspect DIR` keeps
the generated C.

## What is measured

Each workload is one operation over one deterministic corpus, generated
before timing by a SplitMix64 stream that `runner.h` and `goref/corpus.go`
implement byte for byte. Every backend must produce the same checksum
(FNV-1a over the output, or the value itself) in a preflight run before any
timing, and every timed run must reproduce it; the driver refuses to report
a workload whose Oak and Go checksums disagree. Timing covers the operation
over the whole corpus and the checksum, and for the sorts the copy of the
input into the work buffer; corpus generation, compilation, and the process
start are outside. Runs alternate backend order within a sample. Medians
over samples are reported per workload as ns per item, MB/s, and the ratio
of Oak's median time to Go's.

| Workload | Oak | Go | C reference | Corpus at scale 1 |
| --- | --- | --- | --- | --- |
| `sort/random`, `sort/sorted`, `sort/reversed` | `sort_span[u32]` (insertion sort to 16, heapsort above) | `slices.Sort` (pdqsort) | libc `qsort` | 100,000 u32 |
| `varint/encode`, `varint/decode` | `varint_encode`/`varint_decode` (canonical LEB128) | `encoding/binary` `PutUvarint`/`Uvarint` | plain LEB128 loop | 1,000,000 u64, lengths 1..10 bytes uniform |
| `encoding/base64_encode`, `encoding/base64_decode` | `base64_encode`/`base64_decode` (strict, padded) | `encoding/base64` `StdEncoding` | — | 16 MiB random bytes |
| `encoding/hex_encode`, `encoding/hex_decode` | `hex_encode`/`hex_decode` | `encoding/hex` | — | 16 MiB random bytes |
| `encoding/percent_encode` | `percent_encode` (unreserved set, uppercase escapes) | `url.QueryEscape` (allocates) | — | 4 MiB, 70% unreserved, no spaces |
| `hash/sha256` | `sha256` | `crypto/sha256` (hardware SHA-2 on arm64/x86) | — | 32 MiB |
| `hash/crc32c` | `crc32c` (bit-serial) | `hash/crc32` Castagnoli (hardware CRC32C) | — | 32 MiB |
| `random/xoshiro` | `random_next` | a Go xoshiro256** in the harness | — | 100,000,000 draws |
| `random/pcg` | — | `math/rand/v2` PCG (no Oak counterpart; context only) | — | 100,000,000 draws |
| `uuid/v7_format` | `uuid_v7` + `uuid_format` | a Go implementation of the same layout in the harness | — | 1,000,000 UUIDs |
| `strings/utf8_validate`, `strings/utf8_scan` | `utf8_validate`, `utf8_decode` loop | `utf8.Valid`, `utf8.DecodeRune` loop | — | 32 MiB, 60/25/10/5% of 1..4-byte scalars |
| `strings/parse_u64`, `strings/append_u64` | `text_parse_u64`, `append_u64` | `strconv.ParseUint`, `strconv.AppendUint` | — | 1,000,000 numbers, 1..20 digits uniform |
| `time/format_rfc3339`, `time/parse_rfc3339` | `format_rfc3339` (9 fraction digits, `Z`), `parse_rfc3339` | `time.AppendFormat`, `time.Parse(RFC3339Nano)` | — | 1,000,000 instants in ±2^61 ns |

The Oak side of each workload is a small `package main` under `oak/<pkg>/`
exposing `bench_*` wrappers that take views and spans and return counts or
checksums; `bridge_<pkg>.c` includes the generated C for that package (`oak_<pkg>.c`) in
its own translation unit (its `main` is renamed away) and fills the
`BenchWorkload` table `runner.c` drives. The Go twins live in `goref/`.
Both runners print one JSON line per preflight and per timed run; the
driver joins them.

## What is not measured

Allocation counts are not instrumented (Go's `QueryEscape` and
`AppendFormat` allocate; Oak writes into caller storage). Core affinity,
frequency, thermal state, and caches are not controlled; the CI runners
are shared virtual machines and their numbers are indicative only. The C
compiler and flags are recorded in the results (`-O2` by default, no LTO,
Oak's generated C and the bridge in one translation unit). Nothing here is
a formal statement about the packages; correctness is a checksum
agreement on one corpus per workload, not a proof.

## Adding a package

Add `oak/<pkg>/{oak.mod,main.oak}` with `bench_*` wrappers, a
`bridge_<pkg>.c` with a workload table, the Go twin in
`goref/workloads.go` under the same workload names and checksum
definitions, and the package name to `PACKAGES` in `run.py`. Corpus
generators must be added to both `runner.h` and `goref/corpus.go`.
Planned once the packages land on `specification`: `float` (shortest
formatting and correctly rounded parsing against `strconv`), `path`
(clean and match against Go's `path`), `url` (parse and resolve against
`net/url`), `grapheme` (segmentation against `x/text`).

See [RESULTS.md](RESULTS.md) for the recorded baselines.
The per-package status table `stdlib/VERIFICATION.md` carries the latest
Oak / Go ratio next to each package's tests and proofs.
