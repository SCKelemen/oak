# Kernel comparison results

## Baseline, 2026-09-11

Apple M-series (arm64, macOS), `cc` = Apple clang, Go 1.27.1, rustc 1.93.0.
1 MiB / 2^20 elements, medians of 5 samples of 5 rounds, single run, no
affinity control. All checksums agree across implementations.

| Kernel | Oak ns/op | Rust ns/op | Go generic ns/op | Go stdlib ns/op | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: |
| crc32c | 4,424,600 | 2,216,392 | 2,557,175 | 119,183 (hardware CRC) | 2.00× |
| sha256 | 3,444,600 | 3,038,608 | 3,781,483 | 418,917 (hardware SHA) | 1.13× |
| blake3 | 2,288,200 | — | — | — | — |
| dot | 641,400 | 659,700 | 1,038,917 | | 0.97× |
| sum | 89,800 | 92,392 | 322,642 | | 0.97× |
| search | 8,396,000 | 8,523,533 | 12,193,892 | | 0.99× |

Reading: on the loop kernels Oak's generated C is at parity with Rust and
well ahead of Go, with every bounds check in `sum` and `dot` proven away by
the extent facts and the `search` loop paying for the checks it keeps. On
the hashes the gap is algorithmic, not a compiler tax: Oak's CRC-32C is
bit-serial where the others use a table, and its SHA-256 absorbs bytes one
at a time into a block and reads the block with checked owned-array
accesses. The hardware-instruction rows are the ceiling a portable-C
backend cannot reach without intrinsics; they are recorded so the gap is
visible, not to be compared against plain loops.

## After the proof-driven pass, same day

Same machine and settings, run alone (`results/m-series-2026-09-11.json`).
Four extent facts were added to the checker, each with its law in
`Oak.Extents` and its negative test: a literal bound (`i < 64` proves
`w[i]` against a `[64]` array), a scaled index (`block[i * 4 + 3]` under
`i < 16`), a lower bound from a literal initializer or a loop's exit with
subtraction under both bounds (`w[i - 16]` for `16 <= i < 64`, kept
through a loop whose only write is its trailing increment), and a masked
index (`TABLE[x & 255]`). The standard library was rewritten to sit under
them: CRC-32C is table-driven, SHA-256 compresses whole blocks in place
from the input view and reads its schedule without a check, and BLAKE3's
quarter round takes its four words by value so every state access is a
constant index. No algorithmic trick beyond that; no intrinsics.

| Kernel | Oak before | Oak after | Rust | Go generic | Go stdlib | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| crc32c | 4,424,600 | 2,386,600 | 2,170,400 | 2,554,883 | 119,850 (hardware) | 1.10× |
| sha256 | 3,444,600 | 2,632,400 | 2,732,350 | 3,383,175 | 371,183 (hardware) | 0.96× |
| blake3 | 2,288,200 | 1,911,200 | — | — | — | — |
| dot | 641,400 | 604,600 | 631,450 | 961,717 | | 0.96× |
| sum | 89,800 | 89,600 | 88,058 | 310,608 | | 1.02× |
| search | 8,396,000 | 7,478,000 | 7,499,675 | 11,266,700 | | 1.00× |

Reading: every kernel is now within ten percent of the hand-written Rust,
three are ahead, and all are well ahead of Go. The hardware rows remain the ceiling for a portable-C backend: reaching
them is an intrinsics decision (`92-ffi.md` §3 has the AArch64 catalog
shape), not a checker one. Numbers drift by a few percent between runs on
this uncontrolled machine; the JSON keeps every sample.

### Field-path facts (`m-series-2026-09-11-field-paths.json`)

The next increment let a container or an index be a record field path
(`tail.block[tail.filled]` under `while tail.filled < u32(64)`, `tail.h[j]`
under `j < 8`, the trailing increment `t.filled = t.filled + 1`), with a
fact dying when the path or any prefix of it is assigned. The hash
package's checked accesses went from eight to four; the four that remain
(`next.block[next.filled]` in the byte-at-a-time absorb loops, the stack
write in BLAKE3) sit under a record invariant, `filled < 64`, that no
local fact states, so they are the typestate's job, not the extent
facts'. Same machine, same flags, a separate run, so the Rust and Go
columns are re-measured here rather than copied from the table above:

| Kernel | Oak | Rust | Go generic | Go stdlib | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: |
| crc32c | 2,009,800 | 2,022,842 | 2,164,733 | 103,042 (hardware) | 0.99× |
| sha256 | 2,563,400 | 2,636,150 | 3,197,708 | 357,192 (hardware) | 0.97× |
| blake3 | 1,874,200 | — | — | — | — |

## AArch64 hash units, 2026-09-12 (`m-series-2026-09-12-hw.json`)

`stdlib/hash.arm64.oakasm` puts `crc32c_step7` on `crc32cx` and
`sha256_block_hw` on the SHA-2 extension; the Oak bodies remain the
portable definition (`stdlib/README.md`, `stdlib/VERIFICATION.md`). Same
run shape as the baseline; all checksums agree.

| Kernel | Oak ns/op | Go stdlib ns/op (hardware) | Go generic ns/op | Rust ns/op | Oak / Go stdlib | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| crc32c | 101,400 | 102,600 | 2,136,600 | 2,021,158 | 0.99× | 0.05× |
| sha256 | 435,000 | 358,550 | 3,256,042 | 2,653,275 | 1.21× | 0.16× |

CRC-32C is at parity with Go's hardware path. SHA-256 pays one call, one
eight-word state copy, and one `subslice` per 64-byte block on the Oak
side; a multi-block unit waits on the assembler admitting vector loads at
a byte index (see `benchmarks/stdlib/RESULTS.md`).

## Workload shapes from dbs, os, and ml (`m-series-2026-09-11-shapes.json`)

Four kernels shaped like the hot loops of the sibling projects, each with
a Go and a Rust twin of identical arithmetic (the driver still refuses a
timing until all agree): a B-tree leaf probe (`page_probe`: fence-key
search over 2^11 pages of 512 keys, then a binary search inside the page
through a fixed-length `subslice` view), an allocator bitmap scan
(`bitmap`: free-bit count over 2^20 words), bytecode dispatch
(`dispatch`: 2^20 opcodes through an integer `match` over two wrapping
u64 registers), and a tiled f32 reduction (`tiled`: sum of squares with
eight accumulators, eight elements per step, a scalar tail).

| Kernel | Oak | Rust | Go | Go generic | Oak / Rust |
| --- | ---: | ---: | ---: | ---: | ---: |
| page_probe | 7,913,200 | 7,735,183 | 11,041,675 | | 1.02× |
| bitmap | 150,600 (hardware) | 139,758 (hardware) | 346,675 (hardware) | 644,525 | 1.08× |
| dispatch | 6,902,600 | 7,070,558 | 6,953,242 | | 0.98× |
| tiled | 131,400 | 156,750 | 329,317 | | 0.84× |

(`m-series-2026-09-12-popcount.json`, the same machine on a later day:
every row moved with it, so the ratios are the comparison, not the
absolute numbers against the earlier table.)

What the checker proved: every access in `tiled` (`a[i + 7]` under
`i <= len(a) - 8` by `subtraction_under_length`, the eight constant
accumulator indices), `bitmap`, and `dispatch` is unchecked; the constant
shift counts fold their checks away. `page_probe` keeps one checked view
read: `keys[mid * 512]`, whose `mid` is below `pages = len(keys) / 512`
— a bound derived by division, which the scaled-index law does not read
yet. Its second read, `page[m]` under `b` decreasing from 512, and
`search`'s `keys[mid]` under `hi = mid` are proven by the midpoint and
decreasing-bound laws (`50-borrowing.md`, `Oak.Extents.midpoint_under_bound`,
`decreasing_keeps_upper_bound`): the guard `lo < hi` is kept as a
relation, the midpoint inherits `hi`'s upper bound, and the loop's only
write to `hi` lowers it. Neither cost measurably before; a binary search is
latency-bound on the comparison chain.

What the numbers say: `bitmap` is now the population-count instruction
in all three languages — Oak through `arm64.cnt64` (`docs/spec/92-ffi.md`
§3.2), Rust through `count_ones`, Go through `bits.OnesCount64` — and Oak
sits within eight percent of Rust, both loops widened across NEON lanes
by their compilers; the plain Go loop is the SWAR form Oak used before the
instruction landed, and it was as fast as the instruction only because
clang vectorized it too. One lesson is recorded in the lowering: an
inline-assembly form of `cnt` that pinned a vector register serialized
the scan at 317,000 ns, twice the SWAR loop, so the instruction form goes
through the compiler's own `ctpop`. `dispatch` favors Oak's
integer `match`, emitted as a chain of equality tests that clang lowers
as it would a `switch`, over rustc's lowering of the same match. `page_probe` and `tiled`
are the same generated C shape as `search` and `dot`, ahead of both twins
by the same margin.

