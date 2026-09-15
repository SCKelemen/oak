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

The fourth: the checker reads the guard `len(v) >= i + K` in the shape the
generator spells it (`add wS, wI, #K; cmp wL, wS; b.lo`) as the slack fact
`i + K <= len`, so the eight byte reads of `crc32c_word_at` under
`len(chunk) >= at + 8` keep no guards of their own — the 56-byte chunk
step drops from about 500 to 386 instructions. The 22× of the baseline
was not the guards: that build lowered `crc32c_step7`, a function that
`dispatch`es on the `crc` feature, natively as its portable table loop,
fifty-six table lookups per chunk; upstream since leaves a dispatching
function to the C backend, which keeps the selection, so the hardware
`crc32cx` unit is reached again. Measured on the same object (loaded
machine, best samples): `crc32c` 1.8× the C backend, `dot` 1.0×, `tiled`
0.67×, `sum` 2.75×. The fifth: the word assembly is one wide load
(`nativegen/word_fusion.go`; the verifier models a load wider than the
element as the assembly, `Oak.Assembler.wide_load_assembles`) — the chunk
step is 178 instructions, `sha256` 0.92× of the C backend, `blake3` 1.00×;
`crc32c` itself did not move (1.86×), so its remaining cost is the two
calls per 56-byte chunk (the chunk step, then the dispatching `step7` in
the C shell) with their spills, where clang inlines the chain — item 3
below.

The sixth: the inliner substitutes a literal argument for a parameter the
helper never assigns (`compiler/inline.go`), and the extents checker, the
generator and the Oak-side lowering fold `T(a) + T(b)` exactly, so the
seven `crc32c_word_at(chunk, u32(k))` of a chunk read
`chunk[u32(k) + u32(3)]` under `len(chunk) >= u32(k) + u32(8)`: every byte
proven under the caller's `len(chunk) >= 56`, each word one
`ldr x, [xB, #k]` with no index register and no slack guard, each `?`
test a `cmp wL, #k+8`. The chunk step is 117 lines against 140; the timing
row did not move on the loaded host (0.217 against 0.213 ns/byte, the C
backend at 0.151).

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
5. **The typechecker's extent fact for `len(v) >= i + K`** (`word_at`'s
   guard with `i` a parameter): the C backend keeps the eight checked
   accessors and the fused native load keeps its own slack guard, since
   neither side's prover reads that guard as the bound; the fact would
   drop both.

## After the first native program, 2026-09-16

The same harness on the merged compiler (`results/m-series-2026-09-16-native.json`),
the machine carrying a load average near 50 from other work, so the
medians are noisy and the best samples are what is read. Best samples, ns
per operation, 1 MiB / 2^20 elements; the ratio is the native backend over
the C backend (clang `-O3` over the emitted C).

| Kernel | C backend | oak-native | native / C | Rust | Note |
| --- | ---: | ---: | ---: | ---: | --- |
| sum | 111,600 | 357,200 | 3.20× | 110,875 | the multi-accumulator reduction (item 1) |
| dot | 876,000 | 989,000 | 1.13× | 810,342 | from 3.2× at the baseline |
| tiled | 171,800 | 166,000 | 0.97× | 196,817 | from 2.7×; ahead of Rust |
| search | 8,579,800 | 12,278,800 | 1.43× | 7,399,925 | from 2.4× (upstream's proof-guided elision); bounds through arithmetic (item 2) |
| page_probe | 9,262,200 | 11,833,200 | 1.28× | 12,318,975 | as `search`; ahead of Rust |
| bitmap | 183,600 | 161,400 | 0.88× | 170,142 | the C shell on both rows (`arm64.cnt64`) |
| dispatch | 9,757,600 | 7,807,000 | 0.80× | 8,042,433 | ahead of both |
| crc32c | 102,000 | 137,400 | 1.35× | 2,169,192 (table-driven) | the two calls per chunk (item 3) |
| sha256 | 483,800 | 538,600 | 1.11× | 4,125,483 (word-at-a-time) | array parameters stay in the C shell |
| blake3 | 2,631,600 | 4,193,400 | 1.59× | — | array parameters stay in the C shell |

Reading: five of the ten kernels are within 15 percent of clang or ahead
of it on the native backend, three are ahead of the hand-written Rust, and
the three that remain behind by more than a third are the three named
items of the program — the reduction, the bounds facts through arithmetic,
and the call chain — plus the array-parameter bodies (`sha256`, `blake3`)
that the native lane does not lower yet and the C shell runs.

## Bounds through arithmetic, 2026-09-16

`search` and `page_probe` now elide every element guard (the midpoint
below `hi`, `hi = mid` at most the length, `mid * 512` inside the span
under `mid < len / 512`; docs/spec/94-assembler.md §7). The two kernels
re-measured under the same load (`results/m-series-2026-09-16-bounds.json`,
best samples, ns per operation):

| Kernel | C backend | oak-native | native / C | Rust |
| --- | ---: | ---: | ---: | ---: |
| search | 7,483,333 | 11,672,000 | 1.56× | 8,161,264 |
| page_probe | 6,923,000 | 13,298,667 | 1.92× | 8,029,611 |

Reading: the guards were not the cost. A guard that never traps is a
compare and a branch the predictor learns; the binary search is bound by
the dependent load and by its branch shape, and the native inner loop
carries five branches per probe step against clang's two:

```
loop_6:                          ; the native inner loop, guards elided
  cmp w7, w23 ; b.hs done_7      ; lo < hi
  cbnz w24, done_7               ; !found — tested every iteration
  sub/lsr/add → w25              ; mid
  ldr x26, [x19, w25, uxtw #3]
  cmp x26, x6 ; b.ne else_8
  movz w24, #1 ; b endif_9       ; found = true, then back to the header
else_8:
  b.hs else_10                   ; k < target
  add w7, w25, #1 ; b endif_11   ; lo = mid + 1
else_10:
  mov w23, w25                   ; hi = mid
endif_11: endif_9:
  b loop_6
```

Clang lowers the same body with a `csel` pair for the two-way assignment
and leaves the loop directly where `found` is set. The item ahead of
`search` and `page_probe` is therefore the branch shape, three
optimizations LLVM's middle end performs: **if-conversion** of a
conditional chain whose arms each assign a variable and nothing else
(`csel`, reusing the guard's compare — the flags survive the arms), **jump
threading** of an arm that sets a flag the loop condition tests next
(`found = true` leaves the loop), and **branch chaining** (an unconditional
branch to a label followed by an unconditional branch retargets; the
chained `b endif_11; endif_11: endif_9: b loop_6` is one branch). The
bounds facts stay necessary: they are what makes the guard-free form
admissible, and the if-converted arms must keep the facts they had.

## If-conversion, 2026-09-16

The conditional chains of both search kernels lower as one compare and a
select per variable (docs/spec/94-assembler.md §9 "If-conversion"): the
binary search's inner loop is thirteen instructions with the header's two
exits and the back edge as its only branches, the page probe's outer loop
twelve with one exit. Two runs under a load average near 70
(`results/m-series-2026-09-16-select-a.json`, `-b.json`; best samples, ns
per operation; medians were up to twice the bests and are not read):

| Kernel | C backend | oak-native | native / C | Rust |
| --- | ---: | ---: | ---: | ---: |
| search (a) | 7,483,333 (prior run) | 7,186,667 | 0.96× | 7,532,056 |
| search (b) | 9,881,333 | 8,705,667 | 0.88× | 9,549,653 |
| page_probe (a) | 6,964,000 | 11,362,667 | 1.63× | 9,982,569 |
| page_probe (b) | 7,188,667 | 12,639,667 | 1.76× | 9,004,903 |

Reading: `search` went from 1.56× of clang to parity or ahead, and ahead
of the hand-written Rust, once its inner loop had no branch to predict;
the guards' elision (the previous section) was the precondition, the
branch shape the cost. `page_probe` remains 1.6–1.8×: its inner loop
still tests the `found` flag at the header every step (`cbnz`), builds
the constant `1` for the flag inside the loop (`movz w10, #1` per
iteration, a loop-invariant clang hoists), and copies the midpoint before
scaling it (`mov w10, w23; lsl w10, w10, #9` where `lsl w10, w23, #9`
serves); and each probe's page walk touches eleven cache lines four
kilobytes apart, a memory cost both backends pay. Next in this kernel's
order: loop-invariant constants hoisted to the loop's preheader, the
copy-before-shift fused, and the exit flag once the verifier's loop
summary admits a break path.

## Verified reduction unrolling, 2026-09-16

`bench_sum` is the first kernel rewritten before lowering under a proof of
the rewrite (docs/spec/94-assembler.md §9 "Reductions";
`spec/lean/Oak/Reduction.lean`): the plain integer reduction becomes a
four-accumulator main loop, a remainder loop, and the combine, the
verifier proving the assembly against the rewritten body (two loops
coupled inductively, all five element reads elided under the checker's
facts) and Lean proving the rewrite equal to the sequential sum. Run
under a load average near 30 (`results/m-series-2026-09-16-reduction.json`,
best samples, ns per operation):

| Kernel | C backend | oak-native | native / C | Rust |
| --- | ---: | ---: | ---: | ---: |
| sum | 114,000 | 180,333 | 1.58× | 122,167 |
| dot | 875,667 | 971,333 | 1.11× | 820,667 |

Reading: `sum` went from 3.20× of clang to 1.58×. The main loop is
nineteen instructions per four elements — the header recomputes `len(v)
- 4` each iteration (a loop-invariant clang hoists), each of the last
three loads is preceded by its own index add (`add w10, w3, #1; ldr x10,
[x19, w10, uxtw #3]`), and the four accumulators are four `add`s where
clang's NEON `add v.2d` does two lanes per instruction. Next in this
kernel's order: the element address formed once per block (`add xA, x19,
w3, uxtw #3`) with the four loads as two `ldp` pairs off it — the
checker already admits a wider access through a region a slack guard
marked four lanes deep — then the invariant hoisted out of the header,
and the vector form of the same rewrite (the `simd` types the language
has) once the verifier couples a lane sum.

## Select forms, 2026-09-16

The three costs named above for `page_probe` are gone from its loops
(docs/spec/94-assembler.md §9 "If-conversion"): `found = true` is `csinc
w26, w26, wzr, ne` with no constant built in the loop, `hits = hits +
u32(1)` under the Bool is `cmp w26, #0; cinc w4, w4, ne` with no branch,
and `mid * u32(512)` is `lsl w10, w23, #9` reading the midpoint where it
lies. The inner loop is thirteen instructions with the header's two exits
and the back edge as its only branches, the outer twelve with one exit.
The run (`results/m-series-2026-09-16-select-forms.json`) fell under a
load average above 80 — `page_probe`'s C row itself moved from 7.0 to
10.3 million ns — so its ratios are not read; the instruction shapes are
the evidence, and the kernels are re-measured with the next quiet run.
`search` stayed at parity with clang (7.97 against 7.36 million ns, best
samples) with the hand-written Rust at 5.98 in this run.
## Pair loads, 2026-09-16

The unrolled reduction's four loads are two `ldp` pairs off one block
address, and the main loop's header reads the span's length register in
place (docs/spec/94-assembler.md §9 "Pair loads"): `bench_sum`'s main
loop is twelve instructions per four elements, proven as before (the
verifier reads a pair load as two loads, in a loop body too). Run under
a load average between 40 and 75 (`results/m-series-2026-09-16-pairs.json`,
best samples, ns per operation):

| Kernel | C backend | oak-native | native / C | Rust |
| --- | ---: | ---: | ---: | ---: |
| sum | 221,333 | 200,000 | 0.90× | 116,139 |
| dot | 898,000 | 1,028,000 | 1.14× | 910,250 |
| tiled | 204,333 | 217,333 | 1.06× | 253,167 |

Reading: the run is noisier than the previous one (the C row itself
moved), so the ratio is read against the shape: `sum` is at twelve
instructions per four elements where clang's NEON loop is about six per
four (two `ldp q`, two `add v.2d` per eight elements); the remaining gap
is the vector form of the same reduction. `tiled` and `dot` are
unchanged by this increment (their loads are float lanes, which the
pair pass leaves alone).

## The pilots under the native backend, 2026-09-16

The three test systems (github.com/SCKelemen/dbs, os, ml) built with `oak
build -native` and measured against their own baselines, on the machine
carrying a load average between 60 and 180 from other work (ratios within
one run are comparable; runs are not).

**dbs, frame scan** (`tools/bench-frame-scan/run.sh`: read and validate
every frame of a 64 MiB segment, CRC-32C and the SHA-256 chain; the Zig
engine is 1.00×). At the start of the day the native build did not link
(`out[0] = time.time_source_native()`, #469) and, once it did, ran at 208
ms against the C backend's 122. With the inliner reaching an
index-assignment's target (#470) and the loop-invariant pass (#471):

| Backend | min ms | ns per byte | vs Zig |
| --- | ---: | ---: | ---: |
| Oak, C backend under clang | 112.0 | 1.78 | 0.44× |
| Oak, native | 131.7 | 2.26 | 0.76× |
| Zig | 170.0–252.7 | | 1.00× |
| Go | 181.4–195.7 | | |

The native scan is within 18 percent of the C backend and ahead of Zig
and Go; the two rows ran minutes apart, so the ratio to Zig differs
between them.

**os, stage-2 page tables** (`zig build bench-stage2-native
-Doakc=…`): the decoder cycle's cost was `alloc_table`'s page-zeroing
loop (sampled at 87 percent of the cycle), 2048 iterations of `s[dom]
.pages[cell(alloc_idx, j)] = u64(0)`, lowered as 35 instructions with a
call to `cell` per element: 6.7× Zig where the C backend runs 0.57×. The
inliner fix removed the call (22 per element), the loop-invariant pass the
global's address and value, the stride constant, the element address and
its guard (9 per element, `str xzr` the store): 1.57× Zig at the last
measurement (875 against 556 ns per cycle), the C backend 0.43×. The
pilot's `translate` benchmark, a different loop, runs 2× the C backend
natively (7.3 against 4.8 ns per op under this load) and is the next
thing to sample. Clang
zeroes the page in five instructions per element and, with the store
vectorized, fewer; the store loop's unrolling with `stp` pairs is the
next item for this shape.

**ml, emit pilot** (`run.sh`): passes with every compiler of the day
(bit-exact against its oracle); it is an emitter, not a kernel, and has
no timing.

## Arrays as values, 2026-09-16

Owned arrays of scalars now cross the native boundary as values
(docs/spec/94-assembler.md §9 "Arrays as values"), which moves the whole
SHA-256 path of the dbs frame scan — `sha256_rounds`, `sha256_compress`,
`sha256_block`, `sha256_compress_view`, `sha256_init`, `sha256_update`,
`sha256_final` — from the C backend to the native lane: the scan's
`oak build -native` leaves 74 bodies to C where it left 89, the chain
hash agrees, and every array-valued body runs under the trusted verdict
(the verifier stops at a result returned through memory, arrays as
records). The scan itself got slower, not faster: interleaved with the
C build under a loaded machine (the compiler suites running), the native
binary scanned the 64 MiB segment in 187–353 ms against C's 99–122 ms,
where the C-hashed native binary before this change stood at 131.7 ms
under the pending loop-invariant work. The reason is in the dump of
`sha256_rounds`, and it is codegen, not the feature. Each `rotr32(x,
u32(7))` — `(x >> n) | (x << (u32(32) - n))` inlined with a literal `n` —
is eight instructions: `lsr w9, w3, #7`, then `mov w10, w3; movz w11,
#32; sub w11, w11, #7; cmp w11, #32; b.hs trap; lsl w10, w10, w11; orr
w5, w9, w10`, because `u32(32) - u32(7)` is not folded (the folder covers
`+` and `*`), so the left shift takes a variable amount with its trap
guard. Clang emits one `ror w5, w3, #7`. Six rotates per round, 64
rounds per block, a million blocks: the difference alone is the gap. The
message-schedule loop also recomputes `add x10, sp, #80` before each of
its five element accesses and guards `w[i - u32(15)]` under `i < 64`
without a lower bound for `i`, the round loop rebuilds `adrl x10,
data_SHA256_K; add x12, x10, #0` each iteration and rotates eight
working variables through seven `mov`s, and the 256-byte copy of
`w_in` is 32 `ldr`/`str` pairs through one register. In order: fold `-`
and recognize the rotate as `ror` (the next increment), the loop
invariants (pending, PR #471) for the frame and table addresses, a lower
bound for the induction variable in the checker so the schedule's back
references need no guard, pair copies for array values.
## Aggregate helpers, 2026-09-16

The native lane's inliner now expands small record- and array-typed
helpers at their calls (docs/spec/94-assembler.md §9 "Aggregate
helpers"); `absorb`'s loop in `TestNativeShapesAggregateInline` drives
`acc.h = step(acc.h, k)` and `fold(acc.h)` with no `bl`, the path
`acc.h` standing for the read-only parameter. Two things the increment
found. First, a defect it exposed rather than made: with
`json_block_lanes` expanded into `json_string_scan`'s loop, the verifier
refuted the lowering (asm 43 against Oak 30 at `len(src)=63`), and the
cause was the loop invariants hoisting a 64-bit constant's `movz` with
its first `movk` only — fixed in #481, which hoists a chain whole; the
scan agrees again on 190 witnesses. Second, on the dbs frame scan the
chain `sha256_compress` → `sha256_block` does not yet fold into
`sha256_update`'s loop: the expanded body declares `sha256_block`'s
`hs: [*]u32 = span(&state)`, a span local that takes a callee-saved pair,
and by then the pair is not there — the `src` view, the parked result
register, the promoted `filled` and `blocks`, the loop counter, and the
loop invariants' reserve hold the file — so the lowering keeps the call,
as the fallback intends (the scan's chain agrees; 70 bodies left to C
where 71 were, 384 proven). The register budget, not the inliner, is the
next lever there: a span local whose pair the body needs across no call
of its own could take scratch registers, and the invariants' reserve
could yield to a declaration that would otherwise refuse the body.
Timings this round are not read: the machine ran other sessions' test
suites throughout (the C build itself moved from 100 to 326 ms).

## Rotates, 2026-09-16

`rotr32(x, u32(7))` inlined is one `ror w5, w3, #7` (docs/spec/94-assembler.md
§9 "Rotates"); the dbs frame scan's native build carries 46 of them, the
SHA-256 round loop is 55 instructions where it was 91, and its six
variable-shift trap guards are gone. The scan did not move (interleaved
with the C build under load, 232–273 ms against 110–137 ms), and the
profile says why: on this machine the rounds are not on the path. Both
builds dispatch the block compression to the FEAT_SHA256 unit, and both
spend their time in `sha256_update` — the tail loop that feeds one byte at
a time into the partial block, which after the 32-byte chain leaves
`filled` nonzero takes every payload byte (the source's bulk path only
runs from an empty block; a realignment fast path is the library's fix,
not the compiler's). Read side by side (`sample` over a twenty-scan loop,
`dbs-loop-native-sample.txt` and `dbs-loop-c-sample.txt`), clang's byte
loop is ten instructions — the `filled` load, its guard, `ldrb`/`strb`,
the increment stored back, `cmp #64; b.ne` — and the native lane's is
fifteen: the increment's result is reloaded from its slot after the store
(`str w9, [sp, #304]; ldr w9, [sp, #304]`), the `== 64` test is `cmp;
cset; cbz` where a compare-and-branch would do, and the block's frame
address is rebuilt each iteration (the pending loop invariants take
that one). Per 64 bytes the native lane then copies `next.h` and
`next.block` into temps (forty `ldr`/`str`), calls `sha256_compress`,
which calls `sha256_block`, which copies `h` again before the unit runs,
and copies the result back twice; clang inlines the chain and moves the
same bytes as `ldp`/`stp` of `q` registers, twenty instructions in all,
building `next` in the caller's result area so no copy remains at the
return. That is the order of the next increments: the slot reload and
the Bool compare in the byte loop, the result built in the `x8` area,
by-reference arguments passed as the caller's own storage when the
callee reads them in place, and pair copies for aggregates.

