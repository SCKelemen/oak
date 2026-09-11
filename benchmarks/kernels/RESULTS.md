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
