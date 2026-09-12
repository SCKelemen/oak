# Standard library benchmark results

## Baseline, 2026-09-12

Measured Oak revision: `03caff729fa15e92d69b9867745e8015ec89e630`, the base
after pattern-defeating quicksort (#173), the table-driven codecs (#172), the
table-driven CRC-32C and in-place SHA-256 with proven accesses (commit
5def923), and the Lean extractor rounds. Same machine and toolchain as the
first baseline (Apple M4 Max, macOS 26.3.1, Apple clang 21.0.0 `-O2`, Go
1.27.1), scale 1.0, five samples per backend, medians; the machine was
running other test suites, so absolute numbers are a little slower than on
2026-09-11 and the Oak/Go ratio is the figure to read. Raw data:
[baseline-2026-09-12-m4max.json](baseline-2026-09-12-m4max.json). The
hashes are also measured against Rust and Go in
[`benchmarks/kernels/`](../kernels/RESULTS.md), which owns that comparison.

| Workload | Oak ns/item | Oak MB/s | Go ns/item | Go MB/s | Oak / Go time | C reference |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| encoding/base64_decode | 1.74 | 575.5 | 1.46 | 682.8 | 1.19× | — |
| encoding/base64_encode | 1.90 | 525.8 | 1.73 | 578.3 | 1.10× | — |
| encoding/hex_decode | 2.03 | 492.6 | 1.66 | 601.1 | 1.22× | — |
| encoding/hex_encode | 2.49 | 401.0 | 2.69 | 371.5 | 0.93× | — |
| encoding/percent_encode | 8.01 | 124.9 | 7.80 | 128.3 | 1.03× | — |
| hash/crc32c | 2.08 | 480.3 | 0.10 | 9610.2 | 20.01× | — |
| hash/sha256 | 2.68 | 373.5 | 0.37 | 2730.6 | 7.31× | — |
| random/pcg | — | — | 3.66 | 2186.3 | — | — |
| random/xoshiro | 0.78 | 10191.6 | 2.57 | 3113.1 | 0.31× | — |
| sort/random | 52.12 | 76.7 | 51.35 | 77.9 | 1.02× | c_qsort 70.7 ns/item |
| sort/reversed | 2.17 | 1843.3 | 1.84 | 2174.9 | 1.18× | c_qsort 15.1 ns/item |
| sort/sorted | 1.89 | 2116.4 | 1.68 | 2379.2 | 1.12× | c_qsort 4.5 ns/item |
| strings/append_u64 | 36.23 | 313.8 | 30.56 | 372.1 | 1.19× | — |
| strings/parse_u64 | 18.36 | 619.4 | 25.85 | 439.9 | 0.71× | — |
| strings/utf8_scan | 5.90 | 169.5 | 3.29 | 304.3 | 1.80× | — |
| strings/utf8_validate | 3.94 | 254.0 | 2.82 | 355.2 | 1.40× | — |
| time/format_rfc3339 | 57.23 | 524.2 | 125.85 | 238.4 | 0.45× | — |
| time/parse_rfc3339 | 19.71 | 1521.9 | 33.56 | 893.9 | 0.59× | — |
| uuid/v7_format | 56.38 | 638.5 | 66.01 | 545.4 | 0.85× | — |
| varint/decode | 7.49 | 733.0 | 10.02 | 548.2 | 0.75× | c_loop 8.0 ns/item |
| varint/encode | 13.55 | 405.3 | 12.50 | 439.4 | 1.08× | c_loop 12.0 ns/item |

What moved since 2026-09-11: base64 decode 6.10× → 1.19×, base64 encode
2.52× → 1.10×, hex decode 4.74× → 1.22× (one table lookup per symbol, one
pass); sort on sorted and reversed input 21× → 1.1–1.2× and random 1.22× →
1.02× (pdqsort with the heapsort fallback); CRC-32C 40.6× → 20.0× and
SHA-256 8.9× → 7.3× (tables and in-place compression; the rest of the gap
is Go's hardware CRC32C and SHA-2 instructions, see the kernels harness).
Everything else is within noise of the first baseline.

## Round two, 2026-09-12: UTF-8

`utf8_validate`, `utf8_count`, and `utf8_decode` now classify a sequence
through a 256-entry lead table (width plus the class of the second byte's
accepted range, Unicode Table 3-7) and two 8-entry range tables instead of
a chain of comparisons followed by `unicode_is_scalar` and `utf8_width`
checks, and the validator consumes eight ASCII bytes per step when the next
word has no high bit set. The interior loads sit under `len(src) >= 4 &&
at < len(src) - 4` (and the eight-byte form), the wrap-free guard the
checker turns into an extent fact, so they compile to `( src ).base[ at + k ]`
without bounds checks; the last few bytes of an input go through a checked
tail that pads missing bytes with zero, which no range accepts.
Acceptance is unchanged and checked against Go's `unicode/utf8` on 1,440
inputs (every width mix at every alignment modulo eight, each with nine
kinds of damage) in `compiler/e2e_stdlib_utf8_diff_test.go`.

| Workload | before ns/byte | after ns/byte | Go ns/byte | Oak / Go before → after |
| --- | ---: | ---: | ---: | ---: |
| strings/utf8_validate | 3.94 | 3.43 | 3.08 | 1.40× → 1.11× |
| strings/utf8_scan | 5.90 | 5.39 | 3.31 | 1.80× → 1.63× |

The benchmark corpus is 60% ASCII by scalar and 37% by byte, so runs of
eight ASCII bytes are rare there (about 2% of positions); ASCII-dominant
text gains far more from the word step. The remaining scan gap is the
per-scalar `Result[TextScalar, TextError]` returned by value and matched by
the caller; a consumer that only needs boundaries can call `utf8_count` or
walk with the same tables through `grapheme_next`.

`varint` was measured with one-byte fast paths for encode and decode and
left unchanged: the gain was inside the noise (encode 1.08× → 1.14×,
decode 0.75× → 0.79× on a loaded machine), below the bar for touching a
loop the extraction proofs on `sam/stdlib-laws` are being written against.
`uuid/v7_format` and `time/format_rfc3339` were not touched; their
generated C shows no cheap win (the cost is the digit loops themselves).

## Normalization, 2026-09-12

The `normalize` package (`import("normalize")`) adds three workloads. Go's
standard library has no normalizer and the module takes no dependency, so
the Go column is a plain allocating transliteration of the UAX #15
definitions over the same Unicode 17.0.0 extract
(`goref/normalize.go`), not a tuned library: read the ratio as "against a
naive reference", not against `x/text`. The corpus is the harness's random
UTF-8 text (60 % ASCII, then two-, three-, and four-byte scalars, most of
them plain); the ASCII quick-check corpus is the decimal text. Output
buffers are sized by the package's own `_size` functions before timing.
M4 Max, clang 21 `-O2`, scale 1, five samples.

| Workload | Oak ns/byte | Oak MB/s | Go ns/byte | Go MB/s | Oak / Go time |
| --- | ---: | ---: | ---: | ---: | ---: |
| normalize/nfc | 29.62 | 33.8 | 74.41 | 13.4 | 0.40× |
| normalize/nfd | 21.32 | 46.9 | 37.20 | 26.9 | 0.57× |
| normalize/is_nfc_ascii | 0.34 | 2923.8 | 0.38 | 2657.6 | 0.91× |

Before the block table that lets a scalar in one of the 4202 property-free
blocks skip every lookup, NFC ran at 36.9 ns/byte and NFD at 24.6 (against
the same reference at scale 0.25). The remaining cost is the per-scalar
decode, the two binary searches for scalars in marked blocks, the run
buffer round trip, and the re-encode; a direct-indexed first-level table for
the Latin and combining-mark blocks would remove most of the searches.

## Hardware hashes, 2026-09-12

`stdlib/hash.arm64.oakasm` realizes `crc32c_step7` (seven `crc32cx` over
the 64-bit words `crc32c_update` folds 56 bytes at a time) and
`sha256_block_hw` (one compression through `sha256h`/`sha256h2`/`sha256su0`/
`sha256su1`) as asm units whose Oak bodies stay the portable definition.
Same machine and toolchain as the baseline above, `--only hash`, five
samples; raw data in
[hash-hw-2026-09-12-m4max.json](hash-hw-2026-09-12-m4max.json).

| Workload | Oak ns/byte before | Oak ns/byte after | Go ns/byte | Oak / Go before → after |
| --- | ---: | ---: | ---: | ---: |
| hash/crc32c | 2.08 | 0.10 | 0.10 | 20.0× → 0.97× |
| hash/sha256 | 2.68 | 0.43 | 0.34 | 7.31× → 1.26× |

CRC-32C is at parity: both sides are bound by the three-cycle latency of the
dependent `crc32cx` chain, and the Oak side's seven-word call amortizes the
call over 56 bytes. The remaining SHA-256 gap is structural rather than in
the rounds: one call per 64-byte block, an eight-word state copied into a
local and back around the call, and a `subslice` per block; Go compresses
many blocks per call. Walking several blocks inside the unit would need the
checker to admit a 16-byte vector load at a byte index (today an indexed
access must move by whole elements of the span's element type), so it waits
on that assembler extension. Off AArch64 and under
`-DOAK_PORTABLE_INTRINSICS` the portable rows of the baseline apply.

## Hot spots, in the order they are worth pursuing

1. **CRC-32C 20× and SHA-256 7.3× slower.** The portable tables are in;
   the remainder is Go's use of the arm64 `CRC32CX` and SHA-2 instructions.
   The path is Oak's `asm` units (native on AArch64 hosts since the
   assembler rounds), guarded by the same checksums the harness already
   verifies; `benchmarks/kernels/` records the Rust comparison.
2. **`utf8_scan` 1.63×.** A boundary-only walk (`utf8_count`) is level with
   Go; the decode loop pays for the `Result` per scalar. A `TextScalar`
   with a sentinel `next == offset` for failure, or a scan API that yields
   values into a caller span in batches, would remove the tag; both are API
   additions rather than rewrites.
3. **`strings/append_u64` 1.08–1.19×** and **`percent_encode` 1.03×**:
   digit-at-a-time loops with a checked store per byte; a two-digits-per-step
   table (as Go's `strconv` uses) and a proven-extent destination window
   would close the rest.

## Next measurements

The `float`, `path`, `url`, and `grapheme` packages have landed and need
workloads (shortest formatting and correctly rounded parsing against
`strconv`; `Clean`/`Match` against Go's `path`; parse and resolve against
`net/url`; segmentation against `x/text`). Linux numbers from the CI
artifact (`stdlib-benchmark-ubuntu-latest`) should be recorded here
alongside the M4 Max once the workflow has run on `specification`.

## First baseline, 2026-09-11 (kept for reference)

Measured Oak revision: `a8ecd2a5ac2688da4524e53c01477c71c13254dc` (the harness
commit itself adds no library code). Machine: Apple M4 Max, macOS 25.3.0
(Darwin 25.3.0, arm64), Apple clang 21.0.0 with `-std=c99 -O2`, Go 1.27.1
darwin/arm64. Corpora at scale 1.0, five samples per backend, medians.
Machine-readable data with raw samples, commands, and the SHA-256 of every
generated C file: [baseline-2026-09-11-m4max.json](baseline-2026-09-11-m4max.json).
Not a dedicated benchmark host: affinity, frequency, and thermal state were
not controlled.

| Workload | Oak ns/item | Oak MB/s | Go ns/item | Go MB/s | Oak / Go time | C reference |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| encoding/base64_decode | 8.29 | 120.6 | 1.36 | 735.9 | 6.10× | — |
| encoding/base64_encode | 4.24 | 236.1 | 1.68 | 594.7 | 2.52× | — |
| encoding/hex_decode | 7.33 | 136.4 | 1.55 | 646.7 | 4.74× | — |
| encoding/hex_encode | 2.10 | 475.1 | 2.59 | 385.7 | 0.81× | — |
| encoding/percent_encode | 7.70 | 129.9 | 7.11 | 140.7 | 1.08× | — |
| hash/crc32c | 3.87 | 258.4 | 0.10 | 10488.4 | 40.59× | — |
| hash/sha256 | 3.00 | 333.2 | 0.34 | 2961.1 | 8.89× | — |
| random/pcg | — | — | 3.55 | 2252.8 | — | — |
| random/xoshiro | 0.78 | 10317.8 | 2.51 | 3185.6 | 0.31× | — |
| sort/random | 60.88 | 65.7 | 50.07 | 79.9 | 1.22× | c_qsort 64.7 ns/item |
| sort/reversed | 36.51 | 109.6 | 1.75 | 2285.7 | 20.86× | c_qsort 13.8 ns/item |
| sort/sorted | 33.56 | 119.2 | 1.55 | 2573.0 | 21.59× | c_qsort 4.2 ns/item |
| strings/append_u64 | 30.38 | 374.2 | 28.40 | 400.4 | 1.07× | — |
| strings/parse_u64 | 16.46 | 691.0 | 23.13 | 491.6 | 0.71× | — |
| strings/utf8_scan | 5.24 | 191.0 | 2.93 | 341.6 | 1.79× | — |
| strings/utf8_validate | 3.50 | 286.0 | 2.63 | 380.1 | 1.33× | — |
| time/format_rfc3339 | 53.09 | 565.0 | 116.50 | 257.5 | 0.46× | — |
| time/parse_rfc3339 | 19.23 | 1559.9 | 31.22 | 961.0 | 0.62× | — |
| uuid/v7_format | 55.82 | 644.9 | 57.67 | 624.3 | 0.97× | — |
| varint/decode | 7.20 | 763.2 | 9.62 | 570.8 | 0.75× | c_loop 7.9 ns/item |
| varint/encode | 13.53 | 405.8 | 11.98 | 458.2 | 1.13× | c_loop 11.8 ns/item |

"Items" are elements for sort, values for varint/decimal/time/uuid, draws
for random, and bytes for the codecs, hashes, and UTF-8 scans; MB/s is over
the workload's byte count (for sort, the 4 bytes per element; for varint,
the encoded length). The paired sample ratios are tight: every workload's
five Oak/Go ratios lie within ±5% of the median, so the ordering below is
not noise, but a shared laptop is not a benchmark host and the absolute
numbers will move.

Oak is ahead or level on the workloads that are plain fixed-width
arithmetic over one pass: xoshiro (3.2× faster; Go's loop has the same
shape, so this is the C compiler versus the Go compiler), RFC 3339
formatting and parsing (2.2× and 1.6× faster than `time`, which allocates
and handles time zones), decimal parsing, varint decoding, hex encoding,
uuid v7. It is behind wherever the Go standard library uses a table, a
hardware instruction, or a smarter algorithm, and wherever Oak's own code
makes two passes or returns aggregates through `Result`.

### Hot spots as seen on 2026-09-11

1. **Table-driven single-pass codecs: base64 decode 6.1×, hex decode 4.7×,
   base64 encode 2.5× slower.** The generated C shows why. `base64_value`
   compiles to a six-way branch cascade per symbol
   (`unit >= 65 && unit <= 90`, then lowercase, digits, `+`/`-`, `/`/`_`),
   and `base64_decode` runs it twice per byte: once inside
   `base64_decoded_size`, which validates the whole input before the first
   store, and again in the decode loop. Go decodes with one 256-entry
   table lookup per symbol in a single pass and reports the error position
   after the fact. The fix is a 256-byte value table (`[256]u8` with 255
   for "invalid") indexed once per input byte, decoding four symbols into a
   24-bit word in one pass with the destination checked once up front
   (the output length is a function of the input length), and the same
   table shape for hex. Both keep the strict-rejection contract; the
   validation pass disappears rather than moving. Expected: within 1.5× of
   Go without SIMD. Bounds checks are not the cost here: the loops already
   compile to `( src ).base[ i ]` under the `i < len` guard.

2. **Sort: 21× slower on sorted and reversed input, 1.2× on random.**
   `sort_span` is insertion sort to sixteen elements then heapsort, and
   heapsort does the same O(n log n) work on any input; Go's `slices.Sort`
   is pattern-defeating quicksort, which detects sorted and reversed runs
   and finishes them in O(n). The generated `sort_sift_down_u32` also
   performs six `oak_span_index_u32`/`oak_span_store_u32` calls per level,
   each with a bounds check, although root, child, and right are provably
   below `end ≤ len`. The fix is pdqsort (or introsort with the pattern
   checks) in `sort.oak`, with the inner partition loop written against an
   unchecked body behind a checked entry as the JSON codecs do; the
   heapsort can stay as the fallback. Expected: level with Go on random
   input, O(n) on presorted input.

3. **CRC-32C 41× and SHA-256 8.9× slower** — resolved 2026-09-12 by the AArch64 units above (0.97× and 1.26×); the portable analysis stands for other targets. `crc32c_update` is
   bit-serial: an eight-iteration inner loop per byte. Go uses the arm64
   `CRC32CX` instruction and reaches 10 GB/s; a slicing-by-8 table (2 KiB
   of u32, eight bytes per step) is the portable answer and typically
   lands at 2–3 GB/s, a 10× gain; the hardware instruction through Oak's
   `asm` blocks would close the rest on AArch64. SHA-256 is a different
   case: at 333 MB/s the portable C is already within about 2× of what a
   table-free portable SHA-256 reaches, and Go's 3 GB/s comes from the
   SHA-2 extension. In the generated `sha256_compress` the message
   schedule `w[i]` and the state `h[i]` are indexed through ten `oak_index`
   bounds checks per round group, and `sha256_compress` takes and returns
   `[8]u32` and takes `[64]u8` by value (`next.h = sha256_compress(next.h,
   next.block)` copies 96 bytes in and 32 out per block). Unrolling the
   64-round loop by four (or eight, so the schedule window sits in
   registers) and passing the block as a view would help portable
   throughput; parity with Go needs the hardware path.

Also worth noting, below the top three: `utf8_scan` is 1.8× behind because
`utf8_decode` returns `Result[TextScalar, TextError]` (a tagged struct)
per scalar and computes the width through nested ternaries; a fused
validate-and-count over ASCII runs, as `json_string_scan` already does for
the codecs, applies here. `percent_encode` is level with Go despite Go
allocating its result. `varint_encode` is 1.1× behind Go and 1.15× behind
the C loop because it computes `varint_size` before writing.

### Next measurements as planned on 2026-09-11

The `float`, `path`, `url`, and `grapheme` packages land after this
baseline and get workloads then (shortest formatting and correctly rounded
parsing against `strconv`; `Clean`/`Match` against Go's `path`; parse and
resolve against `net/url`; segmentation against `x/text`). Linux numbers
from the CI artifact (`stdlib-benchmark-ubuntu-latest`) should be recorded
here alongside the M4 Max once the workflow has run on `specification`.
