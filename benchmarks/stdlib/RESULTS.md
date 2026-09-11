# Standard library benchmark results

## Baseline, 2026-09-11

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

## Hot spots, in the order they are worth pursuing

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

3. **CRC-32C 41× and SHA-256 8.9× slower.** `crc32c_update` is
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

## Next measurements

The `float`, `path`, `url`, and `grapheme` packages land after this
baseline and get workloads then (shortest formatting and correctly rounded
parsing against `strconv`; `Clean`/`Match` against Go's `path`; parse and
resolve against `net/url`; segmentation against `x/text`). Linux numbers
from the CI artifact (`stdlib-benchmark-ubuntu-latest`) should be recorded
here alongside the M4 Max once the workflow has run on `specification`.
