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
shift counts fold their checks away. `page_probe` and `search` are now
unchecked throughout: `search`'s `keys[mid]` under `hi = mid` and the
in-page `page[m]` under `b` decreasing from 512 by the midpoint and
decreasing-bound laws (`50-borrowing.md`, `Oak.Extents.midpoint_under_bound`,
`decreasing_keeps_upper_bound`: the guard `lo < hi` is kept as a
relation, the midpoint inherits `hi`'s upper bound, and the loop's only
write to `hi` lowers it), and the fence key `keys[mid * 512]` by the
quotient bound (`div_bound_scaled`: `mid < pages` with `pages = len(keys)
/ 512`). Neither check cost measurably before; a binary search is
latency-bound on the comparison chain. Re-measured after the proofs
(`m-series-2026-09-12-search.json`, same machine, same day): `search` Oak
6,785,600 against Rust 7,526,742 and Go 11,228,958 (0.90×); `page_probe`
Oak 7,408,800 against Rust 8,890,467 and Go 12,257,867 (0.83×).

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

## Native backend baseline, 2026-09-15

The `oak-native` row (the same kernels through the Oak assembler,
`benchmarks/native/emit`) beside the C backend, on a machine carrying a
load average near 200 from other work — so the absolute numbers are
noise, and only the ratios and the instruction counts are read. Best of
the samples, 1 MiB / 2^20 elements.

| Kernel | C backend | oak-native | native / C | Lowered natively | What the loop does |
| --- | ---: | ---: | ---: | --- | --- |
| sum | 113 µs | 376 µs | 3.3× | whole, proven | 6 instructions per element already; clang unrolls and vectorizes the u64 reduction |
| dot | 797 µs | 2,560 µs | 3.2× | whole, proven | 13 instructions per element: two guards the checker could not admit (`b[i]` under `len(a) == len(b)`), and the f32 accumulator copied through a scratch register twice per iteration |
| tiled | 172 µs | 468 µs | 2.7× | whole, evidence | the eight-accumulator array lives in frame slots (a load and a store per accumulator per iteration), `a[i + k]` loaded twice, `i + k` computed twice |
| search | 9.8 ms | 24.0 ms | 2.4× | whole, evidence | element guards kept (the index guard is lost across the search's statements) |
| page_probe | 10.2 ms | 23.7 ms | 2.3× | whole, trusted | as `search`, twice |
| dispatch | 18.4 ms | 8.1 ms | 0.44× | whole, proven | the native dispatch loop beats clang's over the C backend's checked bytecode reads |
| bitmap | 326 µs | 184 µs | — | C (`arm64.cnt64` in value position) | both rows are the C backend |
| crc32c | 137 µs | 2,995 µs | 22× | partly | the hardware `crc32cx` unit is reached through four levels of calls per step on the native side, where clang inlines the chain |
| sha256 | 608 µs | 912 µs | 1.5× | partly (array parameters stay C) | |
| blake3 | 2.84 ms | 4.91 ms | 1.7× | partly (array parameters stay C) | |

The first change from this table: the checker now admits a second span's
index under a proven length equality (`Oak.Assembler.index_under_equal_len`),
which drops `dot`'s loop from 13 to 9 instructions per element; the second,
reading a float local's register home in place and renaming a float
operation's result into the home (as the integer path already did), drops
it to 8: `ldr, ldr, fmul, fadd s8, s8, s16, add, cmp, b.hs, b`. The third:
an array local whose every use is an element at a literal index becomes
its elements in registers (`acc: [8]f32` is eight accumulators in
`s8`–`s15`), and a squared operand is loaded once — `tiled`'s loop goes from
about twelve instructions per element (a frame load and store per
accumulator, the element loaded twice) to four (`add, ldr, fmul, fadd`),
under a six-instruction header. Measured on the same loaded machine, best
samples: `dot` 1.36× the C backend (from 3.2×), `tiled` 0.35× (the native
loop is now ahead of clang over the C backend's checked reads), `sum`
unchanged at 3.4×.

What remains, in the program's order:

1. **Reductions unrolled with several accumulators** (`sum`): clang takes
   eight elements per iteration into four vector accumulators and adds the
   lanes at the end. The native backend can emit that under the checker's
   slack idiom, but the verifier's loop coupling pairs one Oak variable with
   one register as an affine image; a reduction over a wrapping,
   associative operator needs the image *sum of registers* (`total = r2 +
   r3 + r4 + r5`), a coupling rule with its law in Lean — so the codegen
   and the coupling land together, or the verdict falls to evidence.
2. **Bounds facts through arithmetic** (`search`, `page_probe`): `mid = lo
   + (hi - lo) / 2` under `lo < hi` and `hi <= len(keys)` is below the
   length, which the typechecker proves and the checker cannot follow (it
   has no upper-bound fact on a register that survives the loop label, nor
   the arithmetic step); the guards stay.
3. **Inlining the call chain** (`crc32c`, the utf8 validator): the hardware
   `crc32cx` unit is reached through four levels of calls per step; an
   asm-level inliner with register renaming, or a source-level one with a
   register allocator that keeps the flattened body's locals in registers.
4. **Loop-invariant header arithmetic** (`tiled`'s `len(a) - 8` recomputed
   every iteration under the slack idiom).

