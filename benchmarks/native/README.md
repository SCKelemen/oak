# The native backend against the C backend

The question this harness answers: when the same Oak function is emitted
by the native backend (the Oak assembler alone, `oak build -native`;
`docs/spec/94-assembler.md` §9) instead of the C backend (clang over the
emitted C), how far behind is it, and why? The OS pilot is moving to the
native backend, so this is the gap that decides whether the golden-case
results hold there.

## Numerical optimization experiments

[Measured FMA maps and reductions](exact_fma/README.md) compare C, native
identity, native without map vectorization, and native optimized, with
interleaved timings and raw assembly/verdict reports. At clean revision
`1ef944b1` on an M4 Max, extending map vectorization to checked explicit
FMA improved its f32/f64 kernels by 3.40×/1.70× over the no-map control,
with proven verdicts. Native still trails C. Sequential byte-dot FMA was
slower, so automatic contraction was not enabled. These loaded-host
microbenchmarks do not replace a representative-suite performance gate.

The next increment at `c3c217b6` groups two vectors per map trip, retaining
one-vector cleanup and the scalar tail under `Oak.Map.grouped_eq`. Against
the previous one-vector control, 4,096-element explicit-FMA maps take 12.6%
less time for f32 and 14.3% less for f64 (nine interleaved samples, M4 Max).
Strict multiply/add maps also improve without contraction. Encoded FMA
bodies grow from 156 to 244 bytes, and short-input measurements do not show
a reliable gain. [Raw results and tradeoffs](exact_fma/README.md#two-vector-measurements-2026-09-17)
retain the C comparison, which native still trails, and all selected map
bodies' proven verdicts.

## OS stage-2: unblock input-consuming allocation, 2026-09-17

At baseline `b0b0cdc6`, stage-2 `translate` rejected the reallocated
candidate at `umaddl x0, w11, w9, x0`: the seam did not derive an element
region when the destination consumed the span base. The checker now derives
indexed ADD/UMADDL results from the pre-write facts and installs only the
bounded result after normal invalidation. The same optimizer's reallocated
candidate is selected and remains `proven`; no checks or proof gates were
disabled. The frame stays 80 bytes.

| Selected body | Before | After |
| --- | ---: | ---: |
| `translate` instructions, including prologue/epilogue/trap | 137 | 120 |
| `translate` `mov` instructions | 25 | 8 |
| `alloc_table` / `map_page` / `unmap_page` instructions | 127 / 210 / 339 | unchanged |

The actual OS pilot (`SCKelemen/os` at `37ba2112`) was built using both
compiler binaries, then linked with its unchanged `stage2_native_shim.c`,
`ring_bench_time.c`, and `stage2_bench.zig`; Zig 0.16.0, ReleaseFast, C shim
`-O2`. Seven pairs alternated baseline-first and candidate-first. Each binary
times 20 million translations and two million decoder cycles, with the Zig
oracle in the same process. The M4 Max's load average was roughly 85–108;
the host was not isolated. No compiler builds ran during these samples.

Median translation time was **7.31 → 6.76 ns/op** (7.5% lower), but the
median *paired* candidate/baseline ratio was **0.962** (3.8% lower), with
five of seven pairs improving. Treat this as a noisy trend, not a precise
speedup claim. Decoder medians were 955.4 and 928.2 ns/cycle, with mixed
paired results: **no decoder-cycle gain is claimed**. Its dominant
page-zeroing loop has not changed. All checksums agree, and the candidate
passes all five OS differential tests: round trip, invalid addresses, pool
exhaustion, shadow-model random operations, and three-regime isolation.

[Raw observations and provenance](results/stage2-inplace-m4-max-2026-09-17.json).
To reproduce with each compiler, use the OS pilot's existing
`zig build bench-stage2-native -Doptimize=ReleaseFast -Doakc=/path/to/oak`
from `pilots/oak`, with separate build/cache directories for each compiler;
alternate the resulting binaries. Do not substitute the vendored generated
C for the newly built native object.

## OS stage-2: carry the page-zeroing index, 2026-09-17

Against `40558540`, the proof-gated `carry-loop-index` candidate removes
the repeated `base + j` calculation from `alloc_table`'s zeroing loop.
The carried index and endpoint use modular `u32` arithmetic; every scalar
store and bounds guard stays in source order. The existing verifier proves
the candidate, without a new verification rule or a weakened gate.

| Selected code | Before | After |
| --- | ---: | ---: |
| Zeroing loop instructions per word | 7 | 6 |
| `alloc_table` total instructions | 127 | 128 |
| `alloc_table` frame bytes | 80 | 80 |
| `translate` / `map_page` / `unmap_page` instructions | 120 / 210 / 339 | unchanged |

The extra instruction is setup outside the 2,048-iteration loop. The
unchanged OS pilot and harness (`37ba2112`, same build settings as above)
passed all five differential tests. After one warmup per binary, seven
pairs alternated which binary ran first; no compiler builds or test suites
ran during the samples. System load averaged roughly 41–63, without host
isolation.

**No reliable decoder-cycle speedup is established.** Separate medians
were 973.0 ns baseline and 1099.6 ns candidate, while the median *paired*
ratio was 1.002 and only three of seven pairs improved. Even the unchanged
translation body fluctuated substantially. This records reduced dynamic
instruction work, not a measured OS latency improvement or a claimed
regression from these noisy observations.

[Raw observations and provenance](results/stage2-affine-index-m4-max-2026-09-17.json).

## OS stage-2: eliminate dominated span guards, 2026-09-17

Against `23d355a6`, the proof-gated `elide-redundant-guards` candidate
removes a repeated `cmp wIndex, wLength; b.hs trap` only when an identical
earlier trap guard dominates it, neither operand changes on any path, and
the removed comparison's flags are dead. Calls delimit the analysis. The
first guard still traps before every effect on invalid inputs, and no
memory operation moves or disappears. The unchanged verifier proves each
selected body.

| Selected body | Before | After | Guard pairs removed |
| --- | ---: | ---: | ---: |
| `alloc_table` | 128 | 114 | 7 |
| `map_page` | 210 | 200 | 5 |
| `unmap_page` | 339 | 333 | 3 |
| `translate` | 120 | 116 | 2 |

The actual OS pilot and harness (`37ba2112`, same build settings as the
preceding stage-2 measurements) passed all five differential tests. After
one warmup per binary, seven pairs alternated which binary ran first; no
compiler build or test suite ran during the samples. The non-isolated M4
Max load average was roughly 16–17 at the start/end.

Decoder-cycle medians were **594.1 → 585.8 ns/cycle**. Six of seven pairs
improved; the median paired candidate/baseline ratio was **0.984** (1.6%
lower). Translation medians were 4.40 → 4.38 ns/op, with four of seven
pairs improving and a median paired ratio of 0.993. The decoder result is
a modest measured gain consistent with the smaller proven bodies, not an
isolated-host throughput bound.

[Raw observations and provenance](results/stage2-redundant-guards-m4-max-2026-09-17.json).

## OS stage-2: share record-span element bases, 2026-09-17

Against `15a3a8e0`, the proof-gated `share-record-bases` candidate retains
one computation of `span_base + domain * record_stride` in an otherwise
unused caller-saved register and redirects later local field-address uses to
it. The exact baseline was rebuilt with the candidate compiler and
`OAK_OPT_SKIP=share-record-bases`. The candidate composes only with scheduling
and refuses cyclic machine CFGs; no memory access moves or disappears, and
every selected body remains `proven` by the unchanged verifier.

| Selected body | Before | After | Bases shared |
| --- | ---: | ---: | ---: |
| `alloc_table` | 173 | 173 | 0 |
| `map_page` | 198 | 195 | 1 |
| `reset` | 160 | 160 | 0 |
| `translate` | 114 | 111 | 1 |
| `unmap_page` | 287 | 272 | 5 |

The unchanged OS source and harness passed all five differential tests. Seven
pairs alternated which binary ran first after one warmup each, with no builds
or tests during sampling. On the non-isolated M4 Max, translation improved in
all seven pairs: separate medians were **4.36 → 4.07 ns/op**, and the median
paired candidate/baseline ratio was **0.940** (6.0% lower). Decoder-cycle
results were neutral/noisy: 4 of 7 improved, separate medians 367.7 → 363.4
ns/cycle, median paired ratio 0.998. No decoder-cycle speedup is claimed.

[Raw observations and provenance](results/stage2-record-base-cse-m4-max-2026-09-17.json).

The follow-on matcher also preserves nearby independent instructions which
the scheduler places between `movz`, `movk`, and `umaddl`. Against the same
byte-identical disabled baseline, the current proven bodies are:

| Selected body | Before | After | Bases shared |
| --- | ---: | ---: | ---: |
| `alloc_table` | 173 | 173 | 0 |
| `free_table` | 32 | 29 | 1 |
| `map_page` | 198 | 192 | 2 |
| `reset` | 160 | 160 | 0 |
| `translate` | 114 | 111 | 1 |
| `unmap_page` | 287 | 263 | 8 |
| `walk_leaf` | 145 | 142 | 1 |

That is 39 instructions removed (156 bytes of Mach-O `__text`; the object is
160 bytes smaller after alignment), with all five OS differential tests still
passing. No new runtime result is recorded: the attempted run saw load
averages above 100 and was discarded. Static provenance is recorded in
[the sparse-schedule result](results/stage2-record-base-sparse-2026-09-17.json).

## OS stage-2: share scalar-global addresses, 2026-09-17

The proof-gated `share-global-addresses` candidate retains one exact
`adrp`/`add :lo12:` address for a declared scalar package global on each
call-free dominated region. It runs after scheduling, refuses cyclic CFGs,
uses only an otherwise-unused declared caller-saved scratch, and leaves every
global load/store in place. The same candidate compiler with
`OAK_OPT_SKIP=share-global-addresses` produced the control.

| Selected body | Before | After | Addresses shared |
| --- | ---: | ---: | ---: |
| `check_range` | 66 | 50 | 8 |
| `map_page` | 192 | 166 | 13 |
| `translate` | 111 | 107 | 2 |
| `unmap_page` | 263 | 229 | 17 |

All four selected bodies remain `proven`; every other selected body is
unchanged, and all five OS differential tests pass. Removing 40 address pairs
removes 80 instructions (320 bytes of Mach-O `__text`) and 80 relocation
entries (640 bytes), shrinking the object **7224 → 6264 bytes**. Runtime is not
reported because host load remained above 40 after verification and linking.

[Static observations and provenance](results/stage2-global-address-cse-2026-09-17.json).

## OS stage-2: forward scalar-global reloads, 2026-09-17

The verifier-gated `forward-global-loads` candidate retains an exact
scalar-global store and replaces only its immediately adjacent reload through
the same authenticated address. Narrow reloads become masks; full-width
reloads become moves or disappear. The same candidate compiler with
`OAK_OPT_SKIP=forward-global-loads` produced the control.

| Selected body | Loads before | Loads after | Loads forwarded | Stalls before | Stalls after |
| --- | ---: | ---: | ---: | ---: | ---: |
| `check_range` | 6 | 4 | 2 | 20 | 18 |
| `map_page` | 20 | 15 | 5 | 41 | 34 |
| `unmap_page` | 27 | 21 | 6 | 60 | 52 |

All three changed bodies remain `proven`; every other selected body is
unchanged, and all five OS differential tests pass. The 13 byte reloads become
13 masks, so instruction count, 4,744-byte Mach-O `__text`, 27 relocations,
and the 6,264-byte object are unchanged. Runtime is not reported because host
load exceeded 60 during the controlled artifact build.

[Static observations and provenance](results/stage2-global-load-forward-2026-09-17.json).

## OS stage-2: preflight source loop rewrites, 2026-09-17

Candidate search previously lowered every source-level loop rewrite in every
function, then learned from the emitted body's zero site count that most were
no-ops. The fill rewrite already had an exact checked-source preflight. The
same non-authoritative pattern now covers reduction unrolling/vectorization,
map vectorization/unrolling, fold vectorization, and constant-trip unrolling.
The scan runs once on a private copy after native helper expansion. It only
keeps known no-op configurations out of search; the existing matcher, law,
seam checker, and semantic verifier remain the authorities for every candidate
that is materialized.

The current OS `stage2.oak` at `c44958a7` was compiled sequentially with clean
compiler binaries, baseline `65070a4bbc63c5a713d5d6b1b64900d7f921cfe6`
and this increment, using `oak build -native -verify-fresh -opt-report`. Both
runs bypassed the verdict cache and produced 22 fresh verdicts.

| Whole stage-2 compile | Before | After | Change |
| --- | ---: | ---: | ---: |
| Candidates considered and lowered | 1,324 | 1,049 | -275 (-20.8%) |
| Fresh wall time, one sequential run | 100.93 s | 124.57 s | +23.4% |

The selected candidate and verdict for every function are identical. The two
Mach-O objects are byte-identical, SHA-256
`4148a140faf46bce23df97d337bab61c9095552e55934d266d4e424d1dcb5b38`.
Candidate counts and object identity are the deterministic results. No fresh
wall-time gain is established: verifier time itself rose 74.45 → 94.60 seconds
between those two non-isolated runs.

With separate verdict caches fully warm (22 of 22 hits), three alternating
runs took 30.98, 38.38, and 40.97 seconds before and 33.01, 35.37, and 41.72
seconds after. The after median is 35.37 seconds against 38.38, but only one of
three pairs improved and the median paired after/before ratio is 1.018. That
also establishes no repeatable wall-time win. This increment removes known
no-op search work and reduces its deterministic materialization count; it does
not claim measured end-to-end compiler throughput.

## OS stage-2: remove normalized reload masks, 2026-09-17

The parent-gated `elide-global-load-masks` candidate follows
`forward-global-loads`. It consumes only that pass's exact adjacent narrow
store/mask spelling; the whole-body verifier decides whether the stored Oak
value was already normalized, while the masked form remains available as a
fallback. The same final compiler with
`OAK_OPT_SKIP=elide-global-load-masks` produced the control. Both full builds
used fresh verification with zero of 30 verdicts from cache.

| Selected body | Instructions | Stalls | Static cost | Masks → moves / removed | Verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| `check_range` | 46 → 44 | 18 → 16 | 70.0 → 67.0 | 0 / 2 | proven |
| `map_page` | 159 → 157 | 34 → 32 | 252.5 → 249.5 | 3 / 2 | proven |
| `unmap_page` | 218 → 216 | 48 → 46 | 347.0 → 344.0 | 4 / 2 | witnessed |

The thirteen masks become seven moves and six deletions. Mach-O `__text` and
the complete object both shrink by 24 bytes (4600→4576 and 6120→6096), with
27 relocations unchanged. `unmap_page` retains its pre-existing witnessed
trap-domain/node-budget result; this transform does not weaken it. Every other
selected body is unchanged, and all five OS differential tests pass. Runtime
is intentionally unreported because final-build load averages were 176–214.

[Static observations and provenance](results/stage2-global-load-mask-elision-2026-09-17.json).

## OS stage-2: clean final scheduled copies, 2026-09-17

The verifier-gated `post-schedule-cleanup` candidate reruns the established
block-local copy/branch cleanup after scheduling and the final scalar-global
passes. It introduces no new rewrite rule. The same final compiler with
`OAK_OPT_SKIP=post-schedule-cleanup` produced the control; both artifacts used
fresh verification.

| Selected body | Instructions | Stalls | Static cost | Cleanup sites | Verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| `check_range` | 44 → 44 | 16 → 16 | 67.0 → 67.0 | 0 | proven |
| `map_page` | 157 → 154 | 32 → 32 | 249.5 → 246.5 | 3 | witnessed |
| `unmap_page` | 216 → 212 | 46 → 46 | 344.0 → 340.0 | 5 | witnessed |

The selected bodies lose seven instructions in total. The unmap transform
reports five locally removed sites, while the selected-body delta is four
because candidate composition changes relative to its disabled fallback.
Mach-O `__text` shrinks 4420→4392 bytes, and object alignment makes the full
object shrink 5944→5912 bytes; all 27 relocations remain. The current stricter
verifier leaves the two loop bodies witnessed on their existing root
trap-domain obligations, not because cleanup weakened them. Every other
selected body is unchanged, and all five OS differential tests pass. Runtime
is intentionally unreported because the host load average exceeded 50 during
final validation.

[Static observations and provenance](results/stage2-post-schedule-cleanup-2026-09-17.json).

## The case

`utf8_valid.oak` is `stdlib/utf8.oak`'s validator with its four lookup
tables passed in as one 64-byte view (`valid_with`): the native backend
does not address package-level arrays yet, and the kernel is otherwise
what the C backend runs at simdutf's speed. `bench_utf8.c` times it over
the state-machines harness's 64 MB of valid UTF-8, best of five; `emit`
writes the native C and companion object the way the end-to-end tests
build (the CLI's `-emit-c` writes the C alone). `run.sh` does everything.

## Results

Apple arm64, 2026-09-16, the two backends and the native lowering before
vector operands were read in place (`94-assembler.md` §9), alternated
three times on a host at load average 370; the ratios are the claim.

| Backend | ns/byte | GB/s | valid |
| --- | --- | --- | --- |
| C backend, clang `-O2` over the emitted C | 0.10–0.11 | 8.8–9.6 | yes |
| Native backend, before (1641e9a8) | 0.17–0.18 | 5.5–6.0 | yes |
| Native backend, vector operands in place, `movi` splats | 0.12–0.14 | 7.3–8.0 | yes |

The validator's body went from 611 lines to 330: fifty `orr` register
copies (every vector read into a scratch and every result back to its
home) to none, fifty frame-slot loads and stores to thirty-six, twenty-six
constant splats from `movz; and; dup` to one `movi` each; every unit stays
proven at the bit level. What remained then was the slot traffic of the
five vector locals the register file did not hold. That is gone; see the
next section for what is left, which is not it.

## Map vectorization against the C backend, 2026-09-17

`run_map.sh` compared the vectorized maps with the scalar loops the
search keeps when `vectorize-maps` is withheld, which says the transform
works but not whether it reaches what clang makes of the same Oak. The
script now builds a third row through the C backend. All three in one
invocation, 2^20 elements, best of seven rounds of two hundred calls:

| kernel | `vectorize-maps` | C backend | scalar loops |
| --- | ---: | ---: | ---: |
| `add_k` | 0.092 ns/element | 0.080 | 0.413 |
| `bump` | 0.103 | 0.090 | 0.410 |
| `fmadd_k` | 0.105 | 0.085 | 0.413 |
| `sum_ab` | 0.150 | 0.152 | 0.425 |
| `xor_mask` | 0.022 ns/byte | 0.023 | 0.412 |

Four to five times over the scalar loops. That much is solid; the
native-against-C column is not, and the row above overstated it.

**The noise floor, measured.** Ten runs of one binary on one kernel,
`add_k`, at 2^12 elements on this machine at load 59:

```
0.065 0.077 0.063 0.131 0.120 0.083 0.065 0.067 0.072 0.079
0.067 0.068 0.063 0.070 0.063 0.066 0.065 0.067 0.073 0.081
```

The same code, twice as slow at the top of the range as at the bottom,
and a 32 percent spread even discarding the two outliers. A difference
of fifteen to twenty-four percent from a single invocation is therefore
not a result. Take the table as parity within the noise on all five, and
the four-to-five-times over the scalar loops — an order of magnitude
clear of the floor — as the only claim it supports.

The lesson generalizes to everything timed here at these sizes: alternate
the binaries inside one invocation, repeat, and treat anything under a
third as unresolved until the machine is quiet. The rows above that
report a factor of two or more are safe; the ones that report tens of
percent from a single run are not.

Where the gap is, in `add_k`:

```
clang                                 native
  ldp  q1, q2, [x10, #-0x20]            add  x10, x2, w5, uxtw #2
  ldp  q3, q4, [x10], #0x40             ldr  q16, [x10]
  add.4s v1, v1, v0                     add  x9,  x0, w5, uxtw #2
  add.4s v2, v2, v0                     add.4s v16, v16, v8
  add.4s v3, v3, v0                     str  q16, [x9]
  add.4s v4, v4, v0                     add  w9,  w5, #0x4
                                        add  x10, x2, w9, uxtw #2
                                        ldr  q16, [x10]
                                        ...
```

The disassembly below still stands as a description of what the two
backends emit, and the instruction difference is real whatever the clock
says here. What is not established is the size of its cost.

Two things the native form does not do. It forms an address per access —
an index add and an address add for every load and every store — where
one base and an immediate offset would serve, which is what the
`vector-blocks` transform exists for and it does fire on these loops — the fused
`[base, #0x10]` form is in the emitted code — but only for some of the
pairs: the rest are refused because the lowering reuses one general
register as both a block address and an index (`x10` holding the address
while `mov w10, w6` writes the same register's W view), and the
transform will not fuse across a write to the address it keeps. And it
has no paired vector load: clang moves 64 bytes in two `ldp q` with the
pointer advanced by the post-index, where the native form issues four
loads and four address computations. `ldp` is modeled for X and W
registers only (`asm/arm64.go`), so the pair form is a seam change —
the instruction, its semantics, and the checker's memory rule — not a
lowering one.

At 2^20 elements these loops are close to memory-bound, which is why
four times the instructions costs only a fifth of the time. The place to
measure either fix is an L1-resident size.

## Where the validator's last 1.27x is, 2026-09-17

Re-measured on the same 64 MB input after the increments since:

| Backend | ns/byte | GB/s |
| --- | ---: | ---: |
| C backend, clang `-O2` over the emitted C | 0.11 | 8.76 |
| Native backend | 0.14 | 7.33 |

The recorded cause no longer holds. The validator's main loop reads four
`ldr q` and advances sixty-four bytes, and its only memory operands are
those four loads: no frame slot is touched between the loop label and the
back edge. The twenty-nine `sp` accesses in the unit are all prologue,
epilogue, and blocks outside the loop. Vector operands read in place
closed that.

What is left is dependency height, and the compiler already measures it.
The search's own report for `valid_with`:

```
selected schedule+reallocate (proven, cost 125.5; identity 142.0)
  schedule+reallocate   instructions 101, loads 4, stores 4, stalls 17
  schedule              instructions 103, loads 4, stores 4, stalls 18
```

Seventeen stalls, and scheduling sixty-six sites removes one of them.
The loop is 108 instructions for 64 bytes, and at 0.14 ns a byte that is
roughly 39 cycles on a 4.4 GHz core for those 108 instructions — about
2.8 issued a cycle, on a core that will do two or three times that. It is
not short of work to issue; it is waiting.

So the next thing this kernel wants is a scheduler that shortens the
critical path rather than one that fills slots. It is the same lesson as
the chain assignment cap below, from the other side: instruction count
has stopped predicting this backend's speed in either direction.

### What it is not: false dependencies, 2026-09-17

The obvious suspect was register reuse. Scratch registers are handed out
last-in-first-out, so a released temporary comes straight back: the
validator's main loop wrote 24 registers in 108 instructions with 81
redefinitions, `v16` alone 24 times, and `w9` 73 times over the whole
unit. Every redefinition is a write-after-write edge and every read
between them a write-after-read edge, and the scheduler runs after
allocation, so it cannot break any of them — which looked like the
reason it removes one stall out of eighteen.

Releasing a vector scratch register to the front of the free list makes
the pool round-robin instead, and it does what it should to the code:
the most-written vector register goes from `v16` 35 times to `v29` 16
times, spread across `v16`–`v31`, at the same number live at once. It
makes no difference at all to the clock — 0.10 ns a byte either way,
alternated four times:

| | ns/byte | GB/s |
| --- | ---: | ---: |
| last-in-first-out (as it is) | 0.09–0.10 | 9.7–11.1 |
| round-robin | 0.10 | 9.7–10.2 |

The reason is that this core renames registers in hardware. A
write-after-write or write-after-read hazard on an architectural
register costs an out-of-order core nothing, so spreading the
architectural names spreads nothing real. Only true dependencies —
a value actually feeding the next instruction — are left, and those the
allocator cannot move.

Two things follow. Post-allocation scheduling has less to offer on this
lane than the stall count suggests, since the ordering it is pinned by
is largely false. And the same change is not pointless everywhere: on a
genuinely in-order core a write-after-write hazard does cost, so the
free-list discipline is worth revisiting for the RV64 lane and the MCU
profile, where it can be measured against a core that has no renamer.
It was not landed here, having nothing to show on the lane it was
written for.

Apple arm64, 2026-09-13.

| Backend | ns/byte | GB/s | valid |
| --- | --- | --- | --- |
| C backend, clang `-O2` over the emitted C | 0.08 | 13.2 | yes |
| Native backend, the Oak assembler's code | 0.38–0.40 | 2.6 | yes |

## What the numbers say

- The instructions are the same: every `simd` operation lowers to the
  NEON instruction the C helper wraps (`docs/spec/93-simd.md` §1.4). The
  five-fold gap is structure, and it ranks the native backend's work:
  1. **Inlining.** The kernel is a call tree — `valid_with` calls
     `check_blocks` per step, which calls `check_block` four times, which
     calls `special_cases`. clang flattens it into one loop with every
     vector in a register; the native backend emits the calls, and each
     call spills the live scratch vectors and reloads them.
  2. **Locals across calls.** A function that calls keeps its vector
     locals in sixteen-byte frame slots (AAPCS64 preserves only the low
     halves of v8–v15), so the validator's nine vector locals are loaded
     and stored around every step.
  3. **Guard elision** — measured and found not to matter. The vector
     loads under a loop condition `len(v) >= N && off <= len(v) - N` now
     carry no compares (the checker reads the proof off the condition),
     and the time did not move: 0.46 ns/byte with and without, on a loaded
     machine. The predictor had absorbed the always-taken branches; the
     instructions saved are real, the time is in the calls and spills.
- Two follow-ups were measured and found neutral on this kernel, so the
  ranking above stands. Releasing a local's register or slot after its
  last use and reusing closed scopes' registers (landed) leaves the
  kernel's 164 vector loads and stores exactly where they were: the
  functions call, so their vector locals live in slots whatever the
  reuse. Inlining the block checkers into the validator at the syntax
  level (tried, not landed; upstream has a source-level inliner for
  scalar leaf helpers) made it slower — 0.9 against 0.6 ns/byte on the
  same loaded machine — because the flattened body declares some forty
  vector locals and only a register allocator with liveness could keep
  them in the thirty-two registers; without one they spill. The
  prerequisite for closing the gap is therefore an allocator that keeps
  vector (and scalar) locals in registers across calls, saving and
  restoring around the call, not more inlining.
- Both backends agree on the verdict, and the end-to-end test
  (`compiler/e2e_native_simd_test.go`) checks every operation's result
  against the C backend, so the gap is speed, not meaning.

## The kernels

The same question over `benchmarks/kernels` (the ten kernels timed against
Go and Rust in `BENCHMARKS.md`): `emit` takes the kernel package directory,
so the whole package — the kernels and the `hash` package they import —
goes through the native backend, and the C backend's build of the same
package is the control. The runner is `benchmarks/kernels/runner.c` with
the emitted C included and the companion object linked; the two runners
were run alternately, three rounds each of three samples over three inner
rounds, 2^20 input elements per kernel, and the checksums agree on every
row. An element is a byte for hashes and `dispatch`, an `f32` for `dot`
and `tiled`, and a `u64` for the other kernels. The tables divide elapsed
time by this input element count, not by the buffers' byte sizes.

Apple M4 Max, Apple clang 21.0.0, 2026-09-14, revision aade7acd. The host
was loaded (load average 35–40 from another session's test suites), so
the ratios are the measurement, not the absolute times; `bitmap`, which
is the same C-realized helper (`arm64.cnt64`) on both sides, bounds the
noise at about twenty percent. Raw samples:
`results/kernels-m4-max-2026-09-14.jsonl`.

| Kernel | C backend ns/element | Native ns/element | Native / C | Verdict on the native body |
| --- | --- | --- | --- | --- |
| `crc32c` | 0.144 | 3.311 → 0.817 after the dispatch fix | 23.0 → 5.7 | trusted (indexes a package table) |
| `sha256` | 0.639 | 0.719 → 0.646 after the dispatch fix | 1.12 → 1.00 | trusted (indexes a package table) |
| `blake3` | 3.115 | 4.808 | 1.54 | trusted |
| `dot` | 0.835 | 2.704 | 3.24 | proven |
| `sum` | 0.115 | 0.393 | 3.40 | proven |
| `search` | 11.50 | 20.30 | 1.76 | proven |
| `page_probe` | 11.13 | 21.51 | 1.93 | proven |
| `bitmap` | 0.192 | 0.229 | 1.19 | C helper on both sides (noise floor) |
| `dispatch` | 10.82 | 9.03 | 0.83 | proven |
| `tiled` | 0.135 | 0.375 (at 30ca36eb) | 2.8 | witnessed; refuted at aade7acd by a verifier false alarm since fixed upstream (see below) |

**Guard elision falls back per source line (2026-09-15,
`docs/spec/94-assembler.md` §9 "Check elision").** `bench_search` and
`bench_page_probe` had every element guard, because one access in each
— `keys[mid]` under the decreasing bound, the fence key under the
quotient bound — is proven by a law the seam checker cannot read, and
the refusal re-lowered the whole body guarded. The compiler now keeps
the guards of the refused line only: `bench_search` reads `probes[p]`
unguarded (one guard, two instructions, out of its outer loop; the
key read keeps its `cmp; b.hs`), `bench_page_probe` likewise loses the
guard of its probe read and keeps lines 76 and 85. Structural counts
from `OAK_NATIVE_DUMP=1` at 5004065a, whole bodies: `bench_search` 57
instructions and one guard to the trap (from 61 and three before this
and the strength reduction), `bench_page_probe` 93 and two (from 102
and six). The verdicts are unchanged (`bench_search` witnessed, the
loop's `hits` coupling; `bench_page_probe` trusted, the path budget), so
the rows stand; timing on a quiet host with the rerun of the strength
reduction below.

**Condition selection (2026-09-15, `docs/spec/94-assembler.md` §9
"Condition selection").** Negations invert their branch, Bool homes are
tested in place, small constants are compare immediates in comparisons
and match arms, and an in-range bitwise constant is not re-masked.
Structural counts at 5004065a with the per-line fallback above already
in: `bench_dispatch` 68 → 60 instructions (its seven-arm match chain
lost every `movz`), `bench_search` 57 → 54 (`!found` is one `cbnz`, and
the inner loop is eleven instructions from the exit test to the key
load), `bench_page_probe` 93 → 90; `crc32c`, `blake3`, `sum`, `dot`
unchanged. With the compare of a conditional chain reused at its else
label (the checker carrying flags across the label): `bench_search` 53,
`bench_page_probe` 89; with no mask after an unsigned right shift and a
match scrutinee compared from its own register, `bench_dispatch` 58.
Verdicts unchanged (`dispatch` proven, `search`
witnessed, `page_probe` trusted). Timing deferred to the quiet-host rerun.

**A leaf's vector locals in the argument registers (2026-09-15,
`docs/spec/94-assembler.md` §9.af).** The flattened `valid` and
`valid_with` spilled five vector temporaries of the expanded
`check_blocks` to frame slots: forty `str q`/`ldr q` per sixty-four-byte
step of the main loop, forty-one in the body. Declaration order had spent
the leaf's twenty vector homes before the temporaries were declared. With
v1–v7 as homes too the loop has no q-register frame access and the body
one; both bodies prove as before. The timing row is not updated here (the
host's load average stayed above 90 all day); the protocol is `run.sh`,
best of five, against the 0.28 ns/byte row below.

**Bottom-tested loops (2026-09-15, `docs/spec/94-assembler.md` §9
"Bottom-tested loops").** A loop over one comparison runs its test at the
bottom as a conditional back edge, with the test peeled once before the
loop: one branch an iteration instead of two. Structural counts from
`OAK_NATIVE_DUMP=1`: `bench_sum`'s iteration is `ldr; add; add; cmp;
b.lo` — five instructions and one branch, from six and two — and the
whole body grows by one instruction (the peeled test); `bench_dot`,
`bench_dispatch`, `bench_search` (both loops; the inner conjunction's
tail is `cmp; b.hs done; cbz wF, loop`), `bench_page_probe` (both loops),
and `bench_tiled` (one loop) rotate the same way. With the widening's
redundant self-move and the result's scratch copy gone the same day,
the whole bodies read: `bench_sum` 20, `bench_dot` 42, `bench_dispatch`
57, `bench_search` 55, `bench_page_probe` 94 (from 20, 41, 68, 61, and
102 before this day's selection work, each now with one branch an
iteration on its rotated loops). Verdicts
unchanged: `sum`, `dot`, `dispatch` proven with their loops coupled
inductively; `search` witnessed; `page_probe` trusted; `tiled`
witnessed. Timing deferred to the quiet-host rerun.

**Invariant exit tests peeled (2026-09-16, `docs/spec/94-assembler.md`
§9 "Loop invariants").** The unrolled reduction's header `cmp wL, #4;
b.lo done; sub wT, wL, #4; cmp wI, wT; b.hi done` ran a length test and a
subtraction every trip and could not rotate. The invariant pass now peels
the length test before the header and hoists the subtraction, the header
is `cmp wI, wT; b.hi done`, and the rotation takes it: `bench_sum`'s
four-way loop is `add; ldp; add; add; ldp; add; add; add; cmp; b.ls` —
ten instructions and one branch a trip, from fourteen and three — and the
remainder loop rotates too, the body proven with both loops coupled (the
verifier reads the peeled test as the loop's entry-only test, so the
loops keep their order). The whole body grows by two (the entry tests
paid once), 38 → 40 by the dump's line count; the trip shrinks by four
instructions and two branches.

**Nested loops weigh their nesting; the probe loops rotate (2026-09-16,
`docs/notes/optimizer-search-2026-09.md`, `docs/spec/94-assembler.md`
§7).** The cost model charged an inner loop's body once for its own
trips and once more inside its outer loop's count — additively — so
rotating `bench_search`'s probe loop priced as a two-point loss and was
never validated. A nested loop's items are now its own and weigh the
product of the trips around them (`LoopWeight` squared at depth one);
the rotated inner loop is the cheaper form by the model and is
selected, witnessed as before. `bench_page_probe`'s rotated form kept
one guard the unrotated one elided: at the rotated loop's header the
entry compared the index against a bound register still holding its
constant (an immediate fact) while the back edge compared it against the
narrowed register, and the meet dropped the disagreeing facts; the meet
reconciles them (`meetIdx`), the page's key read is unguarded under
rotation, and the three-loop body selects the hoisted rotated form
(six percent below the hoisted unrotated one by the model, at the
calibrated loop weight).

**The kernels re-measured (2026-09-16, revision 1fcaba66).** The same
runner and package, seven samples of five rounds, 2^20 input elements per
kernel, with matching checksums. The host was loaded (reported load average
40–50), and this run collected each implementation's samples together,
so both times and ratios may include load drift. Raw samples:
[`kernels-m4-max-2026-09-16.json`](results/kernels-m4-max-2026-09-16.json).

| Kernel | C backend ns/element | Native ns/element | Native / C | Native / C on 2026-09-14 |
| --- | ---: | ---: | ---: | ---: |
| `crc32c` | 0.160 | 0.162 | 1.01 | 5.7 |
| `sha256` | 0.714 | 0.707 | 0.99 | 1.00 |
| `blake3` | 3.211 | 10.117 | 3.15 | 1.54 |
| `dot` | 0.901 | 1.124 | 1.25 | 3.24 |
| `sum` | 0.130 | 0.140 | 1.08 | 3.40 |
| `search` | 11.841 | 12.918 | 1.09 | 1.76 |
| `page_probe` | 9.681 | 16.084 | 1.66 | 1.93 |
| `bitmap` | 0.260 | 0.235 | 0.90 | 1.19 |
| `dispatch` | 10.763 | 9.044 | 0.84 | 0.83 |
| `tiled` | 0.187 | 0.199 | 1.07 | 2.8 |

The loop kernels' measured ratios improved; BLAKE3's worsened from 1.54
to 3.15. The compression-body inspection reported 530 instructions
against 519 earlier that day. That comparison covers two September 16
builds; the September 14 baseline did not lower compression natively.

**BLAKE3 investigation (2026-09-16, compiler e1898e09).** Rebuilding
`aade7acd` shows that only `bench_blake3` and `blake3_start_flag` were
native in its BLAKE3 path: compression stayed in C because the native
backend did not accept its array parameters. The arrays-as-values
increment (`63569c6a`, PR #472) admitted those bodies. The hash source
is unchanged between the baseline and this investigation.

The following comparison uses the same C runner and input, seven samples
of five rounds over 1 MiB, interleaving all five variants and rotating
which runs first. Every sample has the same checksum. The two restricted
current builds use `OAK_NATIVE_ONLY`; their other functions stay in C.
Raw samples, revisions, filters, and emitted native-unit lists:
[`blake3-native-coverage-2026-09-16.json`](results/blake3-native-coverage-2026-09-16.json).

| Build | ms per 1 MiB | Relative to current C |
| --- | ---: | ---: |
| Current C | 2.574 | 1.00 |
| September 14 native baseline, rebuilt | 4.584 | 1.78 |
| Current compiler, only the baseline's two BLAKE3 units native | 3.856 | 1.50 |
| Current compiler, only `blake3_compress` native | 7.085 | 2.75 |
| Current native build | 8.629 | 3.35 |

The coverage experiment identifies native compression as the main added
cost. Keeping the old native coverage restores its approximate ratio;
moving compression alone out of C accounts for most of the gap. The
selected compression body has a 448-byte frame and 527 instructions,
including 156 `ldr`, 141 `str`, 17 `ldp`, 17 `stp`, 34 `eor`, and 32
`ror`; 305 instructions access memory through `sp`. These are counts
from the emitted object, not timings attributed to individual operations.
The verifier reports an indexed load through a record argument without
a dominating constant index guard, so the scheduling and register
reallocation candidates remain trusted and are not selected. The next
compiler work is to discharge that proof obligation and reduce the
compression body's frame traffic; the performance gap is still open.

The baseline rebuild uses the current directory-aware emit driver and
stubs the unrelated `bench_tiled` body, matching its documented historical
verifier refusal; BLAKE3 is unchanged. Core placement and contention
remain uncontrolled. The benchmark driver now actually interleaves
implementations, retains samples in observation order, and checks every
sample's checksum (`benchmarks/kernels/README.md`). The earlier 1fcaba66
record above retains its original samples and sampling order.

**Scalar-array homes released at last use (2026-09-17, baseline
`7060402898b0e17d5191165871d384743ed59a0e`).** Short-lived scalar-replaced
arrays had retained their hidden element registers/slots until scope exit:
the source last-use map names the array, not those hidden locals. Releasing
the actual element homes at the parent's last use lets the next inlined
quarter round reuse them. The synthetic parent still owns no storage and
must never release a frame slot. Loop/branch uses retain their enclosing
statement's lifetime; trailing results remain live.

On Apple M4 Max, the retained change alone gives the following interleaved
comparison (1 MiB, 30 rounds per sample, 15 samples per implementation,
rotating which runs first). Every sample's full checksum agrees:

| BLAKE3 | Before | After | C backend |
| --- | ---: | ---: | ---: |
| Median ms per 1 MiB | 10.707 | 6.639 | 3.020 |
| Repeat run, median ms per 1 MiB | 10.274 | 7.302 | 3.079 |
| Compression instructions | 527 | 406 | — |
| Compression instructions accessing `sp` memory | 305 | 152 | — |
| Compression frame bytes | 448 | 272 | — |

That is 29–38% less elapsed time in these comparisons, not parity with C:
native remains about 2.20–2.37× its time. The native-unit symbol lists are
identical before and after; no added C fallback accounts for the gain.
Two preliminary comparisons measured 38–46% less time with the same
compression body. Those also included a separate integer multiply-add
experiment outside compression, which was removed before the final build.
Core placement, frequency and competing host work were not controlled;
timings of unchanged kernels drift too. Raw rotating samples, binary
hashes, static counts and the rejected experiment are recorded in
[`scalar-array-lifetime-2026-09-17.json`](results/scalar-array-lifetime-2026-09-17.json).

Correctness evidence is deliberately scoped. Direct and selected native
bodies for sequential, loop and branch lifetime fixtures must receive
`proven` verdicts; native/C execution and allocation-pool regressions also
pass. This is not a universal implementation-refinement proof of the
liveness walk. In builds with only the lifetime change, BLAKE3 compression
reports its unguarded indexed-record-load verifier refusal, and its gated scheduling
and reallocation candidates remain unavailable. No proof gate or source
arithmetic semantics changed.

The rejected experiment admitted non-power-of-two integer constants to
`madd`/`msub`/`mneg`. Its overflow fixtures and dispatch body were proven,
and dispatch lost one instruction, but the two timed comparisons were
8.340 → 8.513 ms and 7.837 → 7.819 ms: no repeatable speedup. The matcher
change was removed rather than counting the shorter assembly as a runtime
improvement.

**Constant record indices unblock BLAKE3 optimization (2026-09-17).**
The rejected read was `cv[i]` in compression's final counted loop. The
verifier unrolls that loop, decides its bounds branches, and records no
symbolic guard for the now-constant index. Record loads nevertheless
required that guard. They now select a known element directly after
checking its index against the array field's length; symbolic indices
keep their guard requirement, and reads into a sibling field stay outside.

Compression advances from trusted to witnessed: every verifier witness
agrees, while the full bit-level proof still exceeds the node budget.
The existing optimizer policy admits scheduling and register reallocation
on that evidence. Its emitted body shrinks from 527 to 373 instructions,
with 169 stack-relative memory instructions instead of 305; the frame
remains 448 bytes. Native BLAKE3 coverage is unchanged.

This comparison isolates the verifier fix before the scalar-array lifetime
change above. It rebuilds `fca1c239` with and without the verifier fix,
using the same runner, seven samples of five rounds over 1 MiB, and all
five variants interleaved with rotating starts. The restricted builds
make only `blake3_compress` native. All samples agree, as do checks at 13
input sizes spanning empty input, block boundaries, and chunk-tree
boundaries. Raw samples, source hashes, native-unit lists, and instruction
counts: [`blake3-constant-record-index-2026-09-17.json`](results/blake3-constant-record-index-2026-09-17.json).

| Build | ms per 1 MiB | Relative to C |
| --- | ---: | ---: |
| C control | 2.834 | 1.00 |
| Only compression native, before | 8.479 | 2.99 |
| Only compression native, after | 4.361 | 1.54 |
| Full native build, before | 11.991 | 4.23 |
| Full native build, after | 6.545 | 2.31 |

The full native median falls by 45%, and the restricted build's by 49%.
The M4 Max had a load average of 95–97 and uncontrolled core placement;
the raw samples show substantial scatter. This is a loaded-host result.
The remaining gap includes compression's frame traffic and the surrounding
native helpers; the full proof and parity with C remain open.

Rebased over the scalar-array lifetime change (`a80fe399`), the selected
compression body has 342 instructions, 152 stack-relative memory
instructions, and a 272-byte frame. It retains the witnessed verdict and
agrees with C at the same 13 boundary sizes plus 1 MiB. The timings above
measure the verifier change independently of that lifetime improvement.

The next frame reduction is the message permutation itself. At `2323cc1b`,
the inlined `m = blake3_permute(m)` built a 64-byte literal temporary and
copied it back every round. The in-place cycle lowering
(`docs/spec/94-assembler.md` §9 "In-place array permutations") changes the
selected compression body from 342 to 334 instructions, its stack-relative
memory instructions from 152 to 144, and its frame from 272 to 208 bytes; the
witnessed verdict and native coverage are unchanged. The eight static
instructions are inside the six-round permutation path, hence 48 fewer
instructions per compression. Two interleaved restricted-build runs on the M4
Max agreed on the 1 MiB checksum. Their candidate/base medians were 0.967×
(seven samples, twenty inner rounds) and 0.854× (nine samples, fifty inner
rounds), with wide overlapping ranges under uncontrolled load; the clock says
the change helps but does not support a precise speedup. The raw samples and
the invariant machine-shape counts are in
[`blake3-in-place-permutation-2026-09-17.json`](results/blake3-in-place-permutation-2026-09-17.json).

The full native build also benefits from the permutation change. Two further
interleaved runs compare C, `dfd119cd`, and that same baseline with only the
permutation lowering, using fifteen samples of thirty rounds over 1 MiB:

| Run | C ms per 1 MiB | Native before | Native after | Native elapsed-time reduction |
| --- | ---: | ---: | ---: | ---: |
| 1 | 2.794 | 5.603 | 5.361 | 4.3% |
| 2 | 3.006 | 6.687 | 6.109 | 8.6% |

The timed implementation was developed independently of `a1783bba`. Applying
the landed lowering to the same baseline reproduces the measured native object
and complete runner byte-for-byte; generated C differs only in source-location
comments. All samples agree, and a rebuilt runner agrees with C at fourteen
sizes from empty input through 1 MiB, including block/chunk/tree boundaries.
Native coverage is unchanged. Load averages were 24–25, core placement was
uncontrolled, and sample ranges overlap; these medians do not establish a fixed
speedup. Raw samples and reconstruction hashes:
[`blake3-array-permutation-2026-09-17.json`](results/blake3-array-permutation-2026-09-17.json).

Regression coverage now proves every permutation of five arbitrary words (120
orders), mixed cycles at 32/64-bit signed and unsigned widths, and long cycles.
Gathers and helpers with preceding statements retain snapshot semantics. A
repeated sixteen-word BLAKE3 permutation loop has a proven native body with one
message-array home and passes in native and C builds. These timings predate the full
compression proof described below.

**BLAKE3 compression equivalence (2026-09-17).** The selected standard-library
`hash__blake3_ucompress` now proves all eight returned 64-bit chunks by structural
equality, at the ordinary verification budget. The comparison canonicalizer
spells fixed 32/64-bit rotates as shift-and-OR, recovers a packed high word only
under exact width/count/low-bit bounds, and removes zero-count shifts and
repeated identical masks. This avoids bit-blasting the entire seven-round hash.
The selected companion object is byte-for-byte identical before and after this
verifier change: 330 instructions by the optimization report's count, 144
stack-relative memory instructions, and a 208-byte frame. No runtime speedup is
claimed. `TestNativeBlake3CompressionProven` uses the actual library body and
refutes a changed rotate; `TestE2ENativeBlake3CompressionBoundaries` compares the
compressor-native path and C against the existing reference at thirteen input
lengths from 0 to 5000 bytes, including block/chunk/tree boundaries.

`Oak.BitwiseCanonical` proves the normalization algebra, not a refinement of
the Go canonicalizer or a complete source-to-Arm-ASL execution theorem. The
surrounding hash API is not claimed fully native or proven, and memory-effect
admission, ordering/custody requirements, and the downstream compiler pin are
unchanged. Repeated state traffic and physical message permutations remain
performance work.

**Exact rotate normalization in the verifier (2026-09-17, baseline
`40558540`).** A constant 32/64-bit machine rotate now canonicalizes to
the source's two shifts and or, under the existing
`Oak.AssemblerSemantics.ror_spelling` law. There is no reassociation or
numeric relaxation, no raised budget, and no reordered proof stage.
Independent source/assembly quarter-round fixtures change from witnessed
to proven by structural equality; a wrong rotate count still refutes.

| Scalar quarter rounds | Before, median Verify time | After | Verdict |
| --- | ---: | ---: | --- |
| 1 | 653 ms | 1.64 ms | witnessed → proven |
| 7 | 706 ms | 9.08 ms | witnessed → proven |

Three one-iteration Go benchmark samples per fixture, parsing outside the
timer, same base budget. Before/after groups were not interleaved and host
load/core placement were uncontrolled. Allocation per verification drops
from roughly 1.34 GB to 0.44/0.70 MB respectively because the whole-word
bit-level fallback is avoided. These are **verification costs**, not
application speedups. Full BLAKE3 compression was still witnessed in this
isolated experiment. The later `def4003e` normalization above supersedes
its narrower rotate rule; the independent fixtures/benchmark are retained.
The byte-exact baseline
overlay, source hashes, protocol, proof scope, and raw benchmark output are
recorded in
[`rotate-verifier-2026-09-17.json`](results/rotate-verifier-2026-09-17.json).

**Returned arrays built in the result area (2026-09-17, baseline
`40558540`).** Eligible integer-array locals now use the caller's result
buffer directly, avoiding a separate frame array and its final copy.
Whole-array replacements remain frame-backed, preserving the permutation
optimization above; caller self-assignment still uses snapshot storage.
See `docs/spec/94-assembler.md` §9, "Copies at the boundary", for guards
and proof scope.

Only `hash__blake3_ucompress` was native in these comparisons; the rest
of the unchanged package used C in both variants. Compression changes
from 334 to 308 instructions, 208 to 144 frame bytes, and 170 to 162 static
memory instructions. Stack-relative accesses fall from 144 to 60, but most
of that is a change of memory base to the result buffer, not eliminated
loads/stores. Both measured compression bodies were **witnessed**, not
proven; this historical report predates `def4003e`.

| Interleaved run | Samples × rounds | Before ms / MiB | After | After / before |
| --- | ---: | ---: | ---: | ---: |
| A | 15 × 30 | 4.939 | 4.454 | 0.902 |
| B | 15 × 50 | 4.160 | 4.037 | 0.971 |
| C | 15 × 50 | 4.801 | 4.842 | 1.008 |
| D | 21 × 50 | 4.159 | 4.003 | 0.962 |

All full-digest checks agree with the C control, including 13 boundary
sizes around blocks, chunks and tree merges. Host load and core placement
were uncontrolled; C overlapped local regression suites and D ran after
they finished. Three medians improve, one is effectively flat, with
overlapping sample ranges: a modest gain is plausible, a precise speedup
is not established. These are not whole-native-suite results or proof of
parity with C. The final D C control was 3.065 ms/MiB.
All candidate builds emitted the same compression object, including after
conservative extent/call-lifetime hardening. Raw samples, binary/source
hashes, build protocol, counters and proof limits:
[`blake3-array-result-2026-09-17.json`](results/blake3-array-result-2026-09-17.json).

After integration with `def4003e`, the **same 308-instruction compression
object is proven for all eight result chunks**, with the result-area
optimization retained. The real-compressor wrong-rotate test still refutes,
and native/C boundary tests pass. The object hash is identical to the timed
candidate; the report records this later integration separately rather than
relabeling earlier evidence as proof. The broader upstream canonicalizer
is used directly, without a duplicate rotate rule.

**Frame-pair initializers expose message-word promotion (2026-09-17,
baseline `4d1bc1dd`).** BLAKE3's message array was initialized with 64-bit
pair stores, then accessed exclusively as independent 32-bit words. That
mixed-width initialization alone blocked ordinary frame-slot promotion.
The allocator can now split eligible pair stores using dead, non-reserved,
already-clobbered source registers, preserving the source loads and their
order. Existing dominance, allocation, seam and semantic checks still apply;
an expansion that promotes none of its exposed words is discarded.

The selected compressor promotes 11 slot webs. Static memory instructions
fall **162 → 130**, including **60 → 28** SP-relative accesses, with the
same 144-byte frame. Instructions rise **308 → 311**, and moves rise 4 → 31:
less memory traffic does not imply an equally large runtime improvement.
Both bodies are **proven for all eight result chunks** at the normal budget.
Wrong high-half shifts and a wrong compressor rotate are refuted. Neither
the verifier nor the source reference changed.

Only compression is native in this comparison; the rest of the hash uses
the same C code. Complete 1 MiB BLAKE3, median milliseconds on an M4 Max:

| Same-process run | Samples × rounds | Before | After | C control | After / before |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 51 × 10 | 3.412 | 3.342 | 2.554 | 0.979 |
| B | 101 × 10 | 4.194 | 4.118 | 3.181 | 0.982 |
| C | 201 × 5 | 3.773 | 3.675 | 2.831 | 0.974 |
| D, reversed loading/order | 101 × 5 | 3.711 | 3.643 | 2.822 | 0.982 |

These runs use one thread, rotating interleaved calls to distinct local
libraries, a shared immutable input, one warmup each, and full digest checks
at block/chunk/tree boundaries and after every sample. Affinity, frequency
and external host load remain uncontrolled. The medians of within-sample
after/before ratios show smaller gains in some runs (roughly 1–3%). Earlier
separate-process repeats were inconsistent: ratios **0.998, 0.851, 1.043**.
All samples, including those regressions/outliers, are retained in
[`blake3-frame-pairs-2026-09-17.json`](results/blake3-frame-pairs-2026-09-17.json).
The same-process repeats support a modest host-specific gain, not a universal
speedup: this restricted native path remains about 29–32% slower than C.
The final reserved-register guards and materialization-version update emit
the **same object bytes** as the timed candidate.

Rechecked after integrating `8204e8a9` (paired-load liveness fixes and
constant-trip/scalar-array expansion): an upstream-source overlay and the
rebased candidate emit byte-identical objects to their respective timed
variants, and both generated C wrappers also match. Both still prove all
eight chunks. The integrated materialization version is v13, preserving
upstream's v12 identity change; this later check is recorded separately in
the raw report.

The diagnostic harness is [blake3_same_process.c](blake3_same_process.c).
To reproduce on macOS/arm64, save an emitter built with
`go build -o PATH ./benchmarks/native/emit` at each revision. Run each with
`OAK_NATIVE_ONLY=hash__blake3_ucompress OAK_VERIFY_CACHE=0`, input
`benchmarks/kernels/oak`, and separate output prefixes `before`/`after` in a
fresh temporary directory. Generate the all-C control with
`go run . build -o PATH/control.c benchmarks/kernels/oak`. With those artifacts
as absolute paths in a task-specific `bench_dir`, build and run:

```sh
cc -dynamiclib -std=c99 -O3 -DNDEBUG -Dmain=oak_unused_main \
  "$bench_dir/before.c" "$bench_dir/before.o" -o "$bench_dir/before.dylib" -lm
cc -dynamiclib -std=c99 -O3 -DNDEBUG -Dmain=oak_unused_main \
  "$bench_dir/after.c" "$bench_dir/after.o" -o "$bench_dir/after.dylib" -lm
cc -dynamiclib -std=c99 -O3 -DNDEBUG -Dmain=oak_unused_main \
  "$bench_dir/control.c" -o "$bench_dir/control.dylib" -lm
cc -std=c99 -O3 -Wall -Wextra benchmarks/native/blake3_same_process.c \
  -o "$bench_dir/same-process"
"$bench_dir/same-process" "$bench_dir/before.dylib" \
  "$bench_dir/after.dylib" "$bench_dir/control.dylib" 10 101
```

Use only locally built, trusted libraries; `dlopen` executes library code.
Keep default Mach-O two-level namespaces (no interposition/flat namespace).
For the reverse-order control swap the first two libraries and invert the
result labels when comparing. The harness checks distinct entry points and
uses the generated `View`, `Span`, enum-`Bool` ABI. It is a local diagnostic,
not a portable ABI or a production runtime performance gate.

**Rejected: block-local copy propagation (2026-09-17, baseline
`efb4a203`).** A prototype admits copies from loop-carried/multiple-definition
GPR values when every destination read is later in the same basic block and
the physical source remains unchanged. Tied operands, implicit/nonlocal uses,
source clobbers, narrowing and reserved registers refuse it. Removing a dead
callee-saved copy additionally requires a later full overwrite before any
read, barrier or exit. The existing eight-round simplification limit stays.

This removes six copies from the compressor's seven-round loop:
**311 → 305 instructions**, **31 → 25 moves**. Memory instructions stay at
130 (28 SP-relative), and the frame stays 144 bytes. Both source and candidate
still prove all eight result chunks at the normal budget. Join/loop fixtures,
wrong-result refutation and the machine suite pass. But the clock does not
justify shipping it:

| Sequential same-process run | Samples × rounds | Before ms/MiB | After | After / before |
| --- | ---: | ---: | ---: | ---: |
| C | 101 × 5 | 4.336 | 4.339 | 1.001 |
| D, reversed library order | 101 × 5 | 4.367 | 4.747 | 1.087 |

The medians of within-sample after/before ratios are 1.014 and 1.019;
affinity, frequency and external host load remain uncontrolled. The first
two exploratory sessions overlapped and are **not acceptance evidence**;
their raw samples are retained too. C may overlap a small local test run;
D runs without another local benchmark or compiler test. Every full digest
agrees at the existing block/chunk/tree boundaries and after every sample.
Only compression is native here, with the same C wrapper in both variants.

**The prototype is not enabled or compiled into Oak.** The shipping copy pass
is restored byte-for-byte; no new option or proof-policy change was added.
The [exact prototype and tests](experiments/local-copy-propagation.patch) are
an inert, unapplied patch against the named baseline, kept so a later allocator
or scheduling change can be evaluated without reconstructing this experiment.
In a disposable checkout of that revision, review the patch, use
`git apply --check` before applying, then follow the preceding same-process
build recipe with the baseline and patched emitters. The final safety-tightened
prototype emits the exact timed object. [All raw samples and artifact hashes](results/blake3-local-copies-rejected-2026-09-17.json)
record the proof scope, excluded sessions and rejection. The cause of the
runtime difference is not isolated: fewer moves and smaller code are not, by
themselves, evidence of a faster implementation.

**Loop-scoped array homes (2026-09-17, isolated at `def4003e`).** The
`loop-array-homes` AArch64 candidate preloads selected literal-index elements
of a private frame array, uses scalar registers during one loop, and flushes
written elements before subsequent memory-based uses. Unlike whole-function
scalar replacement, a computed index outside the loop does not disqualify the
array. Selection is deterministic, limited to eight available callee-saved
homes and owned `[1..64]u32/u64` arrays. Borrowed/escaped/whole-reassigned arrays,
nested candidate loops, early exits, ordered blocks, and unknown syntax refuse.
Scalar calls are supported; the home allocator now filters recycled registers
to x19–x28 rather than assuming its reuse pool contains only callee-saved ones.

In this isolated measurement, six BLAKE3 state elements stay in registers:
24 fewer stack loads/stores per round. The selected compressor still proves
all eight result chunks; its frame remains 208 bytes, static instructions fall
330 → 326, and stack-relative memory instructions 144 → 134. The unchanged
Oak source remains the verifier reference. The full search regression checks
nonregression, determinism and retained proof; fixed zero/one/three-trip u32/u64
fixtures prove, and a transform-isolated runtime comparison exercises dynamic
trips, scalar calls, conditional writes, and post-loop computed accesses.
The dynamic nonlinear fixture is witness-checked, not proven. Generic candidate
admission retains the existing verifier gate; this is not a new proof-only policy.

On the M4 Max, two interleaved nine-sample runs at 1 MiB measured median time
reductions of 7.1% and 8.8%; the candidate remained 29.2% and 26.8% slower than
Oak's C backend. At 64 bytes the median reductions were only 0.6% and 2.4%.
Every sample's checksum agrees. Core placement was uncontrolled and host load
was substantial, so these are observations, not a portable speedup guarantee or
the ±8% Zig/Rust/C target. These measurements predate concurrent compiler work;
the [raw samples, configuration and object hashes](results/blake3-loop-array-homes-2026-09-17.json)
pin the exact comparison.

After integration onto `8204e8a9`, default search keeps the upstream direct-result
path: 304 instructions, a 144-byte frame, 60 stack-relative memory instructions,
and all eight result chunks proven. This is a different object from either timed
variant above; no timing claim is transferred to it. Its array is in the caller's
result buffer, which this pass intentionally excludes. The regression permits
competing candidates to win and checks that offering loop homes does not regress
the selected compressor. Private-frame fixtures separately require the home
candidate to fire; result-buffer caching still needs its own justification.

`Oak.LoopArrayHomes` proves preload/read/write/materialize/flush algebra for
arbitrary selected sets and mixed selected/unselected write traces. It does not
prove the Go matcher, private provenance, control flow, register allocator, or
Arm ASL execution. Memory/ordering admission and the downstream pin are unchanged.

**Result-buffer loop homes (2026-09-17, experimental, default off).** A separate
`loop-result-homes` candidate handles the exact named-local returned u32/u64
array, not arbitrary pointer-backed storage. Enable compiler search with
`OAK_NATIVE_LOOP_RESULT_HOMES=1`; `OAK_OPT_SKIP=loop-result-homes` still wins.
It is independently keyed in materialization v15 and verifier-gated, not
shape-neutral. Direct `Lane.LoopResultHomes` is also an explicit experiment.

The first scope is deliberately call-free, with scalar/owned fixed-array
inputs, no mutable-global access, and no address escapes or ordered operations.
Its active loop excludes potentially trapping indices, dynamic shifts,
division/remainder, and float-to-integer truncation. Computed accesses after
the flush remain allowed. Result memory must be ordinary, unpublished storage,
disjoint from inputs and other observable objects; x8 alone proves none of
those properties. See `docs/spec/94-assembler.md` under named-local result
storage for the contract and formal limits.

At base `e29948c5`, the opt-in BLAKE3 compressor selects six homes and still
proves all eight result chunks. The main loop falls from 218 to 203 instructions
and 79 to 67 loads/stores, but the whole body rises from 307 to 308 instructions
and stack-memory instructions from 28 to 46; the frame stays 144 bytes.
The static cost model prefers it (1469 → 1431.5). The existing default
stack-traffic regression test correctly rejected that choice; its bound was
not relaxed. Default search therefore retains the earlier body.
Rebuilding after the trap exclusions and integration onto `26289668` reproduces
both recorded object hashes byte-for-byte: the default body is unchanged, and
the opt-in body is exactly the measured experiment.

Three same-process 1 MiB sessions on the M4 Max did **not** establish a speedup:
the candidate/baseline median ratios were 1.53, 1.27, and 2.01. Host load was
extreme (approximately 183/207/155), with no core affinity, so these are not
stable slowdown estimates either. All boundary and timed digest comparisons
passed. The [complete raw samples and artifact hashes](results/blake3-loop-result-homes-2026-09-17.json)
are retained, including the regressions. No ±8% Zig/Rust/C claim follows.

Fixed zero/one/three-trip u32/u64 cases prove against their unchanged source;
deleting a result flush is refuted. The dynamic 0..7-trip input-snapshot fixture
agrees with C but remains witness-checked. `Oak.LoopResultHomes` proves final
flush equivalence through result-framed, result-blind external steps under
explicit separation/noninterference premises. It does not establish the Go
matcher, caller allocation, traps, shared-memory ordering, or Arm ASL refinement.
Next: improve the register-pressure tradeoff and obtain controlled timings
before considering default promotion. The downstream pin is unchanged.

**Result-home register budget follow-up (2026-09-17).** The experimental
candidate now caps result homes at **two per loop**, independently of private
frame homes (the combined cap stays eight). Integrated materialization v24
records the new recipe alongside upstream extent folding, sparse record-base
sharing, and late-machine flags. It still
requires the same alias, trap and verifier checks and is
still disabled unless `OAK_NATIVE_LOOP_RESULT_HOMES=1`.

Testing budgets 1, 2, 3, 4, 5, 6 and 8 showed that two had the lowest selected
static cost for BLAKE3 (1421). Six homes removed 24 result-memory operations
per round but displaced four message-word promotions. Two homes retain all
11 promotions: compared with six, whole-body SP-memory instructions fall
46 → 30, instructions 308 → 307, and estimated main-loop stalls 18 → 5.
The main loop is 212 instructions versus the default's 218; the 144-byte frame
is unchanged. The budget-three search actually selects no result homes, so
its selected-body proof is not evidence for a three-home implementation.

The timing sessions remain inconclusive: candidate/default median ratios
range from 0.76 to 1.12, including a reversed-load-order control. Against the
six-home body the ratio was 0.96. Host load was high and changing, affinity
uncontrolled, and some early sessions may overlap brief agent builds; even
the final session without our own builds has uncontrolled external load.
The [complete budget sweep, raw timings and hashes](results/blake3-result-home-budget-2026-09-17.json)
are diagnostic evidence, not a reliable speedup or C/Rust/Zig parity claim.
No default promotion follows from the improved static cost.

The existing conditional Lean laws quantify over arbitrary selected sets,
so they are reused without broadening their premises. Regression fixtures now
mix writes to cached and uncached result cells, verify all returned chunks,
refute a missing flush, and compare all 16 runtime cells against an independent
C-only caller computation. Unit tests pin deterministic subset selection,
uncached-memory fallback, independent frame-home capacity and per-loop budget
reset. The isolated two-home BLAKE body retains all eight chunks Proven and
the dedicated fixtures require the bounded homes. Shared-memory ordering,
Arm ASL coverage and the downstream pin are unchanged.

Integration onto `9530ae6f` supersedes that isolated BLAKE comparison: upstream
scalar replacement, inlining and frame-store cleanup select a 283-instruction
body with ten SP-memory instructions, a 160-byte frame, and all eight chunks
Proven. Offering result homes changes neither instructions nor object bytes;
no result homes fire. The BLAKE regression permits this better strategy and
pins the 283/10/160 bounds, while the dedicated fixture uses a computed
post-flush access to keep the actual two-home path covered. This integrated
body differs from all timed variants above: no speedup is transferred to it.

**Strength reduction of constant arithmetic (2026-09-15,
`docs/spec/94-assembler.md` §9.ac).** The `search` and `page_probe` rows
were attributed below to frame traffic; the lowered bodies say otherwise —
neither kernel calls, and every local sits in a register. Their inner
loops paid for arithmetic: `(hi - lo) / u32(2)` lowered as `movz w10, #2;
cbz w10, trap; udiv w9, w9, w10` on the mid-to-load critical path, and
`mid * u32(512)` as `movz; mul`. With the first increment of the
optimization system the same loops read `lsr w9, w9, #1` and `lsl #9`:
`bench_search`'s loop is three instructions shorter and free of the
multi-cycle divide, `bench_page_probe` goes from three `udiv`, two `mul`,
and six `cbz` to three `lsr`, two `lsl`, and three `cbz`, and nine bodies
of the kernel package report `constant operation(s) strength-reduced,
proven` with no fallback. The timing rows are not updated here: the
measurement run on 2026-09-15 found the host at a load average above 200
from other suites, and two byte-identical `sum` bodies timed two-fold
apart across the three runners, so no ratio from it is a result. The
protocol to rerun on a quiet host: the C runner, the native runner from
the previous revision, and the native runner from this one, alternated
over five rounds of five samples at 1 MiB, checksums equal on every row.

What the rows say, in the order they matter:

- **A dispatching function lowered natively lost its hardware unit** (fixed
  in this pass). `crc32c_step7` carries `dispatch { crc: crc32c_step7_asm }`
  (`docs/spec/93-simd.md` §6): the C backend's definition probes the
  processor once and branches to the seven-`crc32cx` unit. The native
  backend lowered the function's Oak body — the portable table walk —
  under the same symbol, and the native build's C compiles the dispatching
  definition out on AArch64, so the unit sat in the object unreachable and
  CRC-32C ran the byte table: 23× behind. The native backend now leaves a
  function with a dispatch clause to the C backend and lowers its callers
  as usual (`compiler/native_bodies.go`, `compiler/e2e_native_dispatch_test.go`).
  `sha256_block_hw` dispatches the same way (`sha2`) and had been lowered
  the same way; after the fix the SHA-256 row is 1.00×, from 1.12×.
- **The remaining CRC gap is byte-wise word assembly.** `crc32c_chunk`
  reads seven little-endian words through `crc32c_word_at`; the native
  body of the chunk helper is 499 lines: 56 `ldrb`s, each behind its own
  `cmp`/`b.hs` guard, shifted and or-ed into a word, although the caller
  established `len(chunk) >= 56` and every offset is a constant. clang
  turns the same source into seven unaligned `ldr`s. Two idioms the
  backend does not have yet: a little-endian word assembled from eight
  guarded byte reads is one load, and constant-offset guards under a
  length fact proven at the call are redundant.
- **Scalar loops are not unrolled or vectorized.** `sum` lowers to the
  tight loop one would write by hand — one `ldr`, one `add`, an increment
  and two branches per element — and `dot` to the same shape with a
  multiply-add, both proven; clang at `-O3` vectorizes both. The 3.2–3.4×
  is the gap between a correct scalar loop and a SIMD one, and it is the
  price of every reduction until the backend unrolls (the register
  allocator across calls from the UTF-8 case is a separate prerequisite;
  these kernels make no calls in their loops).
- **Branchy kernels are within 2×.** `search` and `page_probe` are compare
  and branch chains over loads the predictor cannot help; the native code
  is 1.8–1.9× behind, the difference being the frame traffic around the
  binary-search helper and the guards the checker cannot elide. The
  bytecode `dispatch` kernel measured faster natively (0.83×), a
  difference near the noise band of this host that was not investigated.
- **The hash kernels' wrappers are trusted, not proven**, because every
  path indexes a package-level table (`CRC32C_TABLE`, `SHA256_K`), which
  the verifier does not yet model as memory (`docs/spec/126-verification-chain.md`
  §3). The verdict is the C backend's realization agreeing on the
  checksums, which every row above shows.

**The kernels on a quiet machine (2026-09-17, revision d972d43f).** The
same runner (interleaving the implementations, checking every sample's
checksum), seven samples of five rounds, 1 MiB per kernel, load average
under 7 throughout — the first measurement of the native lane without
another session's suites on the host. Raw samples:
`results/kernels-m4-max-2026-09-17.json`.

| Kernel | C backend ns/byte | Native ns/byte | Native / C | Rust ns/byte | Go ns/byte |
| --- | ---: | ---: | ---: | ---: | ---: |
| `crc32c` | 0.095 | 0.103 | 1.09 | 1.888 | — |
| `sha256` | 0.419 | 0.414 | 0.99 | 2.435 | — |
| `blake3` | 1.759 | 2.312 | 1.31 | — | — |
| `dot` | 0.545 | 0.585 | 1.07 | 0.542 | 0.852 |
| `sum` | 0.087 | 0.087 | 1.00 | 0.082 | 0.280 |
| `search` | 5.225 | 5.901 | 1.13 | 5.296 | 8.792 |
| `page_probe` | 5.441 | 6.107 | 1.12 | 6.258 | 9.487 |
| `bitmap` | 0.135 | 0.129 | 0.96 | 0.126 | — |
| `dispatch` | 6.492 | 5.165 | 0.80 | 6.539 | 6.422 |
| `tiled` | 0.121 | 0.126 | 1.04 | 0.146 | 0.299 |

Every kernel's native body is within thirteen percent of the C backend's
build, `sum` at parity and `dispatch` ahead; `blake3`, with its
compression native since the arrays-as-values increment, is at 1.31
after the night's register homes and in-place permutation (3.15 the
evening before, on a loaded host). Against Rust the native lane is
within a tenth on the loop kernels and ahead on `page_probe` and
`dispatch`; the hashes' gap to Rust is algorithmic (BENCHMARKS.md). The
absolute times are about 0.6 of the loaded runs' — the load, not the
compiler, was the other factor there.

### Selective constant unrolling: not retained (2026-09-17)

At `d735d322`, a 512-node copy-cost heuristic kept BLAKE3's large seven-round
loop rolled and unrolled only the small final mixing loop. This exposed
scalar replacement of the state. The prototype was **not retained**:
fewer memory operations did not produce a repeatable runtime improvement.
Raw samples and artifact identities are in
[the experiment record](results/blake3-selective-unroll-rejected-2026-09-17.json).

The ordinary selection was 287 encoded instructions, ten SP-relative
accesses and a 160-byte frame. Enabling the existing result-home experiment
at this revision produced the identical object. Partial unrolling plus
reallocation instead produced 336 assembler instructions (340 encoded),
a 288-byte frame, and one main loop with 31 loads and 19 stores, against
the ordinary main loop's 32 loads and 32 stores; the final loop disappeared.

The actual partial-unroll candidate was independently seam-checked and
**proven for all eight result chunks**, with the normal verification
budget and no cache hit, before encoding it for measurement. This matters
because ordinary search did not select it: the counter remained in
`[sp, #208]`, so the cost estimator missed its seven-trip bound and used
the default 256 loop weight. The prototype's ordinary search result was
a different, 299-instruction fallback; that was **not** the timed candidate.

The same-process harness loaded separate baseline/candidate/C libraries,
checked every digest byte at fourteen lengths including 1 MiB, then ran
the variants in rotating order. Runs were sequential, without agent
builds or tests during timing; the second reversed library order. Only
compression was Oak-native, with the same C companion for both variants.

| Run | Rounds × samples | Baseline ms/MiB | Candidate ms/MiB | Candidate / baseline | C control ms/MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 30 × 15 | 6.040 | 6.253 | 1.035 | 4.910 |
| B, reversed | 100 × 21 | 6.182 | 7.035 | 1.138 | 4.782 |
| C | 100 × 21 | 6.580 | 7.323 | 1.113 | 5.732 |

These are medians under heavy shared-host load, not clean regression
estimates or a replacement for the quiet-machine suite above. They give
no basis to enable the change. The existing unroll profitability policy
is restored; only generated-name collision guards and their proof/execution
regressions remain. The stack-counter cost gap is a follow-up, not a
performance claim or an implemented change.
Rebuilding with those guards on the measurement base reproduced the
baseline object byte-for-byte, still proven for all eight result chunks.

For reproduction, the inert
[prototype patch](experiments/selective-constant-unroll.patch) targets
`d735d322` and includes the budget tests and the explicit, proof-gated
candidate probe. It is **not** a patch against the final name-guard revision.
The probe uses the historical scratch path `/tmp/oak-hash-next.yX4zpM`;
its encoded object links against the baseline C companion with
`cc -dynamiclib -std=c99 -O3 -DNDEBUG -Dmain=oak_unused_main`.
Use `blake3_same_process.c` with absolute baseline/candidate/control library
paths and the rounds/sample counts above. No experimental flag or weaker
verdict was made a default.

### Small unrolling with stable array placement (2026-09-17)

The follow-up at `c212716f` keeps the pre-unroll array-placement decisions:
BLAKE3's result state stays in the result area and its message words keep
their scalar homes. Only the small final mixing loop expands; the seven-round
loop stays rolled. Unlike the preceding experiment, there is no added frame
traffic: both bodies have a 160-byte frame and ten SP-relative accesses.
The candidate has 324 assembler instructions (328 encoded), versus the
baseline's 283 (287 encoded). Static size alone would miss this opportunity.

The actual candidate passed the ordinary seam check and freshly proved all
eight result chunks before encoding, with no cache hit or larger verifier
budget. The integrated `unroll-small` implementation reproduced its object
byte-for-byte. A regression also requires a changed rotate to be refuted.
The final machine proof uses the partially unrolled body, with the existing
`Oak.ConstantUnroll.loop_eq_unrolled` law licensing the source rewrite;
the pre-unroll tree is only an additional placement refusal.

Three sequential same-process runs compared that candidate, the baseline,
and a C control. Each used 100 calls per sample and 21 samples, rotating the
variants; run B reversed library order. All 32 digest bytes agreed with C at
fourteen lengths through 1 MiB and after every timed sample. No agent builds
or tests ran during timing. Only compression was Oak-native, using the same
C companion for both native variants.

| Run | Baseline ms/MiB | Candidate ms/MiB | Ratio of medians | Median paired ratio | C control ms/MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 7.758 | 6.273 | 0.809 | 0.924 | 5.938 |
| B, reversed | 6.105 | 5.219 | 0.855 | 0.922 | 4.592 |
| C | 6.033 | 5.263 | 0.872 | 0.924 | 4.167 |

The paired statistic is the median of candidate/baseline sample ratios,
not the ratio of the two medians. Both favor the candidate in all three
runs, but the shared host was busy (one-minute load 56.88 before run A),
with large timing spreads. The roughly 7.6% paired advantage is provisional,
not a quiet-host speed guarantee or a whole-native-suite result. Raw samples,
library order, hashes and exact scope are in
[the experiment record](results/blake3-small-unroll-2026-09-17.json).

The strategy is retained as a separate, verdict-gated **experiment**, offered
with `OAK_NATIVE_UNROLL_SMALL=1`; `OAK_OPT_SKIP=unroll-small` suppresses it.
Full `unroll-constant` remains unchanged. Default emission reproduced the
baseline object exactly. Opt-in search still selected that baseline: the
current static model prices the measured candidate at 1570 versus 1523.
In particular, it charges a bounded loop half its maximum trips even for
the final loop that starts at zero and always executes eight times. This
underprices the rolled form. Correctly distinguishing exact trip counts
from upper bounds is a follow-up, not a policy override in this change.
The timings above are therefore **not** timings of opt-in search's selected
body; they are of the independently proven explicit candidate.

For reproduction, the inert
[candidate probe](experiments/small-unroll-probe.patch) adds an opt-in test
to the integrated revision. It loads the checked benchmark package and emits
only after fresh admission and proof. Its historical scratch directory is
`/tmp/oak-stable-unroll.kT73G4`; use a new approved scratch directory when
repeating the experiment. Link its object with the unchanged baseline C
companion using `cc -dynamiclib -std=c99 -O3 -DNDEBUG
-Dmain=oak_unused_main`, then pass absolute baseline/candidate/control library
paths to `blake3_same_process.c` with `100 21`. Broader quiet-host and selection
measurements remain necessary before enabling this strategy by default.

### Exact trip costing selects faster full unrolling (2026-09-17)

At `65070a4b`, the cost model still charged BLAKE3's fixed seven-round loop
as 3.5 trips and its rotated eight-iteration tail as four. The new
`ExactTrips` hint distinguishes a closed counted loop from a mere upper
bound. It covers both top- and bottom-tested unsigned literal comparisons,
rejecting uncertain control flow, entry values, widths and possible wrapping.
The existing upper-bound heuristic remains unchanged for other loops.
This is costing evidence only: source laws, seam checks and semantic verdict
requirements are unchanged.

The result was not simply selection of the preceding small-unroll experiment.
Ordinary search now selects **full constant unrolling + scheduling +
reallocation**, freshly proven for all eight result chunks. Enabling
`OAK_NATIVE_UNROLL_SMALL=1` selects the identical object; small unrolling
remains experimental and was not forced to win. The selected form costs 1973,
against 2834.5 for the old rolled form with its exact trips charged (previously
1523 under the half-bound heuristic).

Static size grows from 283 assembler instructions (287 encoded) to 1175
(1179 encoded); the frame grows from 160 to 288 bytes, with SP-relative memory
instructions increasing from ten to 306. Those counts alone are misleading
here: the old body executes its memory instructions inside seven- and
eight-trip loops. From the assembly and those exact trip counts, its dynamic
loads/stores total 550 per compression, versus 358 in the selected loop-free
body. This is an assembly-derived count, not a hardware-counter measurement.

The actual **search-selected** object was linked with the same C companion
as the baseline. Three sequential same-process runs used 100 calls per sample
and 21 samples, rotating variant order; run B reversed the libraries. All
32 digest bytes agreed with the pure-C control at fourteen boundary lengths
through 1 MiB and after every timed sample. No builds or tests from this
experiment ran during timing, though other shared-host work remained active.

| Run | Baseline ms/MiB | Selected ms/MiB | Ratio of medians | Median paired ratio | C control ms/MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 5.966 | 4.080 | 0.684 | 0.690 | 4.470 |
| B, reversed | 6.458 | 4.896 | 0.758 | 0.771 | 5.247 |
| C | 6.847 | 6.562 | 0.958 | 0.911 | 4.843 |

All three favor the selected output, but the **9–31% paired improvement is
provisional**: load was high (one-minute load 62.35 before run A), timing
spreads were large, and cores/frequency were uncontrolled. This is native
compression within the C hash driver, not a whole-native application result
or a claim of consistent parity with C. Raw samples, artifacts and the
reproduction protocol are in
[the experiment record](results/blake3-exact-trips-2026-09-17.json).

There is a build-time tradeoff. Observed emission rose from 82.3 seconds to
243.2 seconds (246.7 with small unrolling offered). These are loaded-host
observations, not a controlled compiler benchmark. One-second process samples
found candidate materialization in `machine.ReallocateWith`/`Simplify`; final
semantic verification remained below one second. Cheaper search/materialization
of the winning form is follow-up work; the runtime gain does not erase that
cost.

As a broader code-generation check, separate before/after builds allowing
`bench_dot`, `bench_sum`, `bench_search`, `bench_page_probe`, `bench_bitmap`,
`bench_dispatch` and `bench_tiled` produced **byte-identical C and native
companion objects**. This preserves their existing mixed backend/evidence
grades; it is not a claim that all seven are proven native bodies. Compiler
regressions retain the all-chunk proof, wrong-rotate refutation and native/C
boundary checks, with distinct bounded profiles for the measured fully
unrolled output and the original rolled fallback.

These measurements preceded integration of the branch's loop-rewrite preflight
and per-pass checker fingerprint changes. To reproduce the measured comparison,
build one emitter at `65070a4b` and another at that base plus this commit's
exact-trip costing patch; building the current branch also includes those
independent compile-time changes. Use
`OAK_NATIVE_ONLY=hash__blake3_ucompress OAK_VERIFY_CACHE=0 OAK_NATIVE_TIMING=1`
on `benchmarks/native/emit`, using `benchmarks/kernels/oak` as input. Link each
selected object with the unchanged baseline C companion as a local shared
library, using `cc -dynamiclib -std=c99 -O3 -DNDEBUG -Dmain=oak_unused_main`.
Build the pure-C control separately. Run `blake3_same_process.c` with absolute
baseline/selected/control library paths and `100 21`, reversing the first two
paths for run B. No special candidate probe or raised proof budget is needed.

**Independent repeat (2026-09-17).** Three further runs started with a pristine
`732505af` baseline and an independent exact-trip costing prototype. After
integration, a fresh default-mode build of `f07b5f99` emitted **byte-identical
native code and C companion** to the timed prototype. Offering small unrolling
also produced the same object; the winner uses full constant unrolling.

| Run | Baseline ms/MiB | Selected ms/MiB | Ratio of medians | Median paired ratio | C control ms/MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 5.861 | 4.125 | 0.704 | 0.795 | 4.156 |
| B, reversed | 5.077 | 3.632 | 0.715 | 0.759 | 3.815 |
| C | 4.898 | 4.468 | 0.912 | 0.879 | 3.824 |

The same 100-call, 21-sample protocol checked all digest bytes at fourteen
boundary lengths and after every sample. The **12–24% paired improvement**
supports the earlier result under another period of heavy, variable load
(one-minute load 51–175 across run boundaries). Only compression was native;
core placement and frequency remained uncontrolled, and run C remained slower
than C. [The repeat record](results/blake3-exact-trips-repeat-2026-09-17.json)
preserves all samples, the reversed labels for run B, source and object hashes,
fresh all-eight-chunk proof diagnostics, and the reproduction commands.

An additional 3,120-case regression compares recognized trip counts with direct
loop execution across both register widths, test placements, inclusive bounds,
nonzero starts and uneven strides. The loop-array-home competition regression
now uses the measured full-unroll and rolled profiles above, retaining its
proof, stack-count nonregression and deterministic-selection checks.

### Lower allocation cost in reaching definitions (2026-09-17)

The compilation profile above led to `machine.Webs`: reaching-definition
analysis allocated a map at each definition and deep-copied per-register sets
at each block transfer. `Simplify` repeated that work after every propagated
copy. Reaching sets now use immutable sorted slices, with shared singleton
storage and new storage for unions of differing nonempty sets. The analysis,
copy-propagation order, search configuration and proof requirements are unchanged.

Frozen binaries at `8c30d7b6` and that base with this change ran the same
fixtures in before/after/after/before order. Each invocation collected five
samples of three iterations, giving ten samples per implementation. The Webs
fixtures contain 1,024 copy sites; Simplify processes 128 and checks that every
iteration propagates and removes all 128 copies. Medians on the loaded M4 Max:

| Workload | Before ms/op | After ms/op | Before allocations/op | After allocations/op |
| --- | ---: | ---: | ---: | ---: |
| Webs, straight line | 12.929 | 5.349 | 42,962 | 13,612 |
| Webs, 64 blocks | 23.261 | 9.217 | 86,119.5 | 15,820 |
| Webs, loop | 11.296 | 6.752 | 53,929 | 14,177 |
| Simplify, 128 copies | 469.226 | 277.427 | 1,532,974 | 587,662 |

The Webs fixtures use **68–82% fewer allocations** and take 40–60% less time
in these samples. Simplify uses 62% fewer allocations and 33% fewer allocated
bytes, with 41% less elapsed time. These are compiler microbenchmarks.

One full BLAKE3 emission comparison reduced **CPU time from 275.24 to 204.40
seconds (26%)**. Wall time increased from 398.44 to 479.10 seconds while
one-minute host load went from 93→72 during the baseline to 101→170 during the
candidate. This is not a controlled wall-time speedup; scheduling and frequency
were uncontrolled. No other builds or tests from this experiment overlapped
timing. The full process's peak resident size did not decrease.

The emitted **C companion and native compression object are byte-identical**,
including the same full-unroll/schedule/reallocate selection, and both emitters
freshly prove all eight result chunks with the normal budget and cache off.
The change has no runtime-speed claim. Regressions cover 1,024 set unions with
input-storage checks, branch joins, independent successors, loops, unreachable
roots, call clobbers and tied vector operands.

[The experiment record](results/blake3-webs-cost-2026-09-17.json) contains all
microbenchmark samples, CPU and wall observations, resource counters, source and
binary hashes, proof diagnostics and reproduction instructions. The permanent
fixtures are in `machine/webs_benchmark_test.go`.

### One analysis per ordinary copy-propagation round (2026-09-17)

`Simplify` previously rebuilt reaching definitions immediately after moving a
copy's reads, then rebuilt again at the next round. For a copy between different
physical registers, only its single-definition destination becomes unread;
the source remains read by the copy. Dead-code elimination can use the original
webs with that destination excluded. Self-copies retain the full rebuild, and
each next round still rebuilds webs and liveness. Propagation order, width and
availability checks, and the 1,024-round bound stay unchanged.

Frozen binaries at `4b1c1a2d` and that base plus this change ran sequentially in
before/after/after/before order, before later branch integrations. This base
already includes both immutable reaching sets and allocation-proposal reuse.
Ten samples per variant of `BenchmarkSimplifyCopies` (three iterations each,
128 copies checked each iteration) gave these medians:

| Metric | Before | After |
| --- | ---: | ---: |
| ms/op | 289.491 | 179.640 |
| Allocations/op | 587,667 | 375,691.5 |
| Allocated bytes/op | 178,341,397 | 114,416,087.5 |

That is **38% less observed time and 36% fewer allocations and allocated bytes**
for this compiler fixture. Four fresh BLAKE3 compression-only emissions followed:

| Run | Wall seconds | User + system CPU seconds |
| --- | ---: | ---: |
| Before A | 84.29 | 66.13 |
| After A | 73.68 | 60.44 |
| After B | 91.10 | 60.08 |
| Before B | 78.70 | 66.83 |

CPU time fell **9–10%** in the paired observations, with fewer retired
instructions in both. Wall time improved in one pair and worsened in the other;
one-minute host load ranged from 159 to 272, with uncontrolled frequency and
scheduling. No builds or tests from this experiment overlapped timing.

All four native compression objects and C companions are **byte-identical**;
all eight result chunks were freshly proven with the normal budget and no
cached verdicts. The full-unroll/schedule/reallocate output is preserved (the
equivalent recipe label sometimes includes late cleanup). There is no additional
hash-runtime speedup claimed. Regressions compare the cheaper DCE path against
fresh analysis across 142 cases. [The measurement record](results/blake3-simplify-cost-2026-09-17.json)
contains raw samples, per-run load, resource counters, hashes and commands.

## Reusing allocation proposals, 2026-09-17

The preceding full-unroll runtime improvement made candidate materialization
expensive: sibling configurations repeatedly allocated the same machine body
before differing in later scheduling or cleanup. A search-local cache now
reuses that deterministic stage, without changing which proposals are offered
or bypassing their seam checks, costs or semantic verdicts.

On base `8c30d7b6`, before integration of subsequent branch changes, four
separate emitter processes ran in **before → after → after → before** order.
Only `hash__blake3_ucompress` was allowed native. The verdict cache was disabled,
the proof budget unchanged, and both experimental small-unroll and
loop-result-home modes off. `/usr/bin/time -l` measured emission (checking,
candidate search, proof, C-source and native-object writing), not C compilation,
linking or application execution. No builds/tests from this experiment
overlapped the measurements; other shared-host work and uncontrolled cores and
frequency remained substantial limitations.

| Run | Elapsed seconds | User + system CPU seconds | Maximum RSS, MiB |
| --- | ---: | ---: | ---: |
| Before A | 176.95 | 250.19 | 529.6 |
| After A | 57.67 | 66.17 | 542.3 |
| After B | 75.17 | 68.31 | 550.2 |
| Before B | 333.71 | 273.18 | 540.4 |

Total CPU fell **74–75%** in both comparisons, as did retired instructions.
Elapsed time improved in both, but its large variation precludes a stable
wall-clock multiplier claim. Both after runs reused **18 of 22 allocation
requests**, retaining four entries and 1,204,729 bytes of canonical payload.
Peak RSS increased by about 10–13 MiB in the paired observations; the cache is
not free. Its 32-entry/16-MiB limit bounds canonical retained input/output,
**not Go heap usage**.

All four builds produced **byte-identical native objects and C companions**
and freshly proved all eight BLAKE3 result chunks. The full-unroll winner from
the preceding experiment is preserved; this change claims **no additional
application-runtime speedup**. The final before run reported a `late-cleanup`
recipe label while emitting the same bytes as the other three.

A separate seven-kernel before/after check also preserved byte-identical C and
native objects. Its CPU time fell 32.59 → 29.11 seconds while elapsed time rose
25.57 → 29.87 seconds and RSS rose 1370 → 1442 MiB. This single, loaded-host pair
does not establish a general wall-clock benefit. Evidence grades were unchanged:
dot, sum and dispatch proven; search, page-probe and tiled witnessed; bitmap
left to C. Neither this comparison nor allocation reuse promotes weaker grades
to proof.

The key contains exact machine inputs, including every instruction field and
operand, explicit frame objects, clobbers and architecture. Only deeply copied
items, clobbers and reporting counts are retained; each hit keeps the fresh
candidate's source metadata. Trace mode bypasses reuse. Regression coverage
compares cold/hit/uncached AArch64 and RV64 output, checks mutation isolation
and bounded admission, and freshly refutes a deliberately changed candidate
after a hit.

[The measurement record](results/blake3-allocation-reuse-2026-09-17.json)
contains counters, hashes, evidence and commands. Reproduce with emitters built
at `8c30d7b6` and that base plus this commit's allocation-reuse patch. These
timings do not include the independent immutable-reaching-set optimization
above or subsequent verifier/checker changes; the percentages are not additive.
Use
`OAK_NATIVE_ONLY=hash__blake3_ucompress OAK_VERIFY_CACHE=0 OAK_NATIVE_TIMING=1`,
unset any verifier-budget override, and emit `benchmarks/kernels/oak` into
distinct output prefixes. Compare both `.o` and `.c` files, not just diagnostics.

## Rejected late frame-load forwarding, 2026-09-17

At `7b46dba9`, a separate proof-gated AArch64 candidate replaced private-frame
reloads with same-width register moves after scheduling and allocation. It
retained stores, respected physical-register definitions and block/call/memory
boundaries, and preserved W self-moves (which clear the upper 32 bits).
Ordinary search selected it, with **all eight BLAKE3 result chunks freshly
proven** at the unchanged budget and with verdict caching disabled.

Static metrics looked favorable: **44 fewer loads**, 358 → 314 memory
instructions, and estimated cost 1973 → 1840. The frame remained 288 bytes;
the body remained 1175 assembler instructions (1179 encoded). Both native
objects were linked against the byte-identical baseline C companion. Only
compression was native, not the whole hash driver.

Three sequential same-process runs used 100 hashes per sample and 21 samples
per variant, rotating execution order; run B reversed the native library
arguments. All 32 digest bytes matched the fresh pure-C control at fourteen
boundary lengths through 1 MiB and after every timed sample. No builds/tests
from this experiment overlapped timing. The M4 Max was heavily loaded, with
uncontrolled cores/frequency; one-minute load ranged from 66.6 to 170.1 at run
boundaries.

| Run | Baseline ms/MiB | Prototype ms/MiB | Median paired ratio | Faster pairs | C control ms/MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 4.240 | 4.893 | 1.094 | 7/21 | 4.733 |
| B, reversed | 5.093 | 5.386 | 1.075 | 9/21 | 5.458 |
| C | 5.614 | 5.844 | 0.996 | 11/21 | 5.796 |

**Rejected: no repeatable runtime benefit.** The load reductions and proof
did not justify a new default. Heavy host noise prevents assigning a precise
regression percentage or microarchitectural cause, but does not turn these
results into evidence of a speedup. The production prototype and its search
option were removed; the preceding shipping optimizer remains unchanged.
[All samples, hashes and commands](results/blake3-frame-forward-rejected-2026-09-17.json)
and the [reproducible proposal patch](results/blake3-frame-forward-rejected-2026-09-17.patch)
are retained, rather than adding an unmeasured optimizer option to maintain.
The archive targets the measured `7b46dba9` base plus the verifier-only fix
`be68ec04`, not a later optimizer registry; exact reproduction instructions
are in the record.

The experiment did expose a verifier soundness bug worth fixing independently:
zero-extending a previously truncated wide parameter could recover its
discarded high bits. Thus a W-register write could falsely prove a u64 identity
claim. The retained fix keeps an explicit mask, preserves original input-width
provenance, and invalidates older cached verdicts. Regressions prove the actual
narrowing and refute identity, including a W self-move and frame spill/reload.
Explicit conversions fuse the required mask so the existing Lean lowering
representation remains unchanged; the formal model's comment now distinguishes
its masked law from a general widening theorem. No proof budget, gate or source
semantics was weakened. This increment claims **no application speedup**.

Full `asm`, `machine`, `nativegen` and `opt` suites and targeted compiler tests
passed before integration. After rebasing onto `c775cd70`, machine/optimizer
suites, compiler proof/cache/global-forwarding checks and the exact width/lowering
regressions passed again. Fresh default emission on the integrated branch
produced **byte-identical BLAKE3 C and native object files** to the frozen
baseline and independently proved all eight chunks with no cached verdict.

## The refuted kernel

At the measurement revision (aade7acd) the native build refused
`bench_tiled` (an `f32` sum of squares over eight accumulators in an
`[8]f32` local, a stride-8 loop and a remainder loop): the verifier
reported a mismatch at `len(a) = 8`, the asm producing `+Inf` and the Oak
model `0xF66F…`, a negative value a sum of squares cannot produce. The
lowered asm (`results/bench_tiled-native-2026-09-14.asm`) performs the Oak
body's operations in the Oak body's order. The gate was not bypassed for a
measurement (a mismatch rejects the build, by design); the kernel was
reduced instead. Reduced in isolation the refutation did not reproduce at
the current revision, and rebuilding the emitter at aade7acd reproduced it
on the same source, so it was a verifier false alarm that an upstream
commit between aade7acd and dc714aee has since fixed (a bisect narrowed it
to one of `deb20e52` "a counterexample reports the element values the
diagrams chose", `5038ac25`, `e7f6fdb6`; the other two candidates were
build skips). At 30ca36eb the kernel lowers, is witnessed on nineteen
inputs, agrees with the C backend's checksum, and runs at 2.8× the C
backend's time — the same scalar-loop gap as `sum` and `dot`.

## Reduction vectorization, 2026-09-16

The integer reduction's accumulators as vector lanes
(`docs/spec/94-assembler.md` §9 "Reduction vectorization"), measured over
2^20 elements, best of seven rounds of two hundred calls, alternated with
the baseline. The first table's rows were taken on a host at load
average 90–115 while the shape was being chosen; the selected rows were
re-taken at load average 40–55, where the spread is a few percent. Every
row's checksum agrees.

| Form of the `u32` reduction | ns/element | verdict |
| --- | ---: | --- |
| four scalar accumulators (the unrolling, the baseline) | 0.157–0.165 | proven |
| one `simd.U32x4`, four elements an iteration | 0.174–0.198 | proven |
| two `simd.U32x4`, eight elements an iteration | 0.106 | proven |
| four `simd.U32x4`, sixteen elements an iteration (**selected**) | 0.063–0.064 | proven |

| Form of the `u64` reduction | ns/element | verdict |
| --- | ---: | --- |
| four scalar accumulators (the unrolling, the baseline) | 0.186–0.194 | proven |
| four `simd.U64x2`, eight elements an iteration (**selected**) | 0.130–0.145 | proven |

So `u32` runs at 2.6× the scalar unrolling and `u64` at 1.4×, both
proven at the bit level with the lanes coupled as packs to the halves of
their registers.

What the rows say:

- **One vector accumulator is slower than four scalar ones**, though it
  is fewer instructions (six per four elements against ten) and the
  static model prices it cheaper. A 128-bit lane-wise add is one
  loop-carried chain where four scalar adds are four; the interleave, not
  the vector width, is what breaks the chain. The first shape this
  increment tried was the four-element one, and measuring it is what sent
  the rewrite to four accumulators.
- **The combine belongs in the vector domain.** Storing all four
  accumulators into a sixteen-element frame array and summing the lanes
  there is witnessed, not proven (the verifier does not equate the
  results after the loops), and it costs a store and four loads per
  accumulator. Folding the accumulators pairwise with `simd.add` first,
  storing the one vector left, and reading its lanes is proven, is
  fewer instructions, and is what the rewrite emits.
- **The cost model needed calibrating before it agreed.** At its old
  LoopWeight of 32 assumed trips, a sixteen-element main loop's
  fifteen-trip remainder was charged half the work, so no strided form
  could pay for its tail and the model kept the scalar unrolling. The
  weight is now 256, the conservative end of the range where the
  per-element term dominates the tail for every stride the compiler
  emits; the three `u32` rows above are what calibrated it, and the
  model now orders them as measured (`opt/cost.go`).

## Vector block loads, 2026-09-16

The vectorized reduction's four `ldr q` read one element address at the
immediate offsets `#16`, `#32`, `#48` instead of forming an address each
(`docs/spec/94-assembler.md` §9 "Vector block loads"). The `u32` main
loop goes from eighteen instructions for sixteen elements to eleven, and
stays proven.

| `u32` reduction, array size | per-load addresses | one block address |
| --- | ---: | ---: |
| 2^20 elements (4 MiB, streamed) | 0.057 ns/element | 0.057 ns/element |
| 2^12 elements (16 KiB, L1-resident) | 0.044–0.047 | 0.039–0.042 |

The 4 MiB row is bandwidth-bound — 0.057 ns an element over four bytes is
about 70 GB/s — so the address arithmetic was already free in the core's
spare issue slots, and removing seven instructions from the loop buys
nothing there. The L1-resident row is where the instructions show, at
about eight percent. What the increment really buys is the instruction
count itself: code size, instruction cache, and the lanes whose cores
have less spare issue than an M4 (the RV64 lane, an MCU) — the sort of
gain this harness cannot see and should not claim.

## The chain assignment cap, measured and kept, 2026-09-17

If-conversion rejects a chain of more than four assignments
(`maxSelectAssigns`, `nativegen/select.go`), so a three-arm chain
writing two variables branches on its first arm and converts only the
rest. The stated reason is register pressure, and it looked pessimistic:
where every right-hand side is a variable already in a register the
lowering reads it in place and allocates nothing, so the count could
have been of the values that actually need a scratch register. Counting
that way converts the chain whole — eight straight-line instructions in
the loop body against a branch, two moves and four selects — and it is
proven either way.

It is slower. A three-arm chain writing `small` and `big` over 2^12
`u32` elements, best of seven over three runs:

| which arm the data takes | capped (first arm branches) | converted whole |
| --- | ---: | ---: |
| unpredictable, the arms about even | 1.27–1.43 ns/element | 1.27–1.44 |
| always the last arm | 0.79–0.83 | 1.21–1.64 |
| always the first arm | 0.80–0.86 | 1.30–2.29 |

Nothing to gain where the branch is unpredictable, and a factor of 1.6
to 2.8 to lose where it is not. The cap earns its keep for a reason
beyond registers: a branch *skips* the arms after it, while the selects
of a converted chain all execute, and per variable they form a serial
dependency — `csel` feeding `csel` feeding `csel` — that lengthens the
loop's critical path. The two increments above won by removing a
mispredict that cost more than the work they added; this one adds work
and removes a branch that was already free.

So the cap stays, and the measurement is the argument for it. The
per-variable serialization is also the thing a port-pressure or
dependency-chain term in the cost model would have to capture
(item 26); the static instruction count says converted is cheaper here,
and the clock says otherwise in two rows out of three.

## Chain condition operands, 2026-09-16

A three-arm chain whose second condition needs a computed operand,
`x < lo ? { a = x } | x + 1 < hi ? { a = hi } | { a = lo }`, inside a
loop. The whole chain is if-converted where before the first arm branched
and only the remainder was (`docs/spec/94-assembler.md` §9
"If-conversion"): twelve body instructions with two branches become
eleven with none.

| three-arm chain over 2^12 `u32` elements, best of seven over three runs | half converted | converted |
| --- | ---: | ---: |
| the comparisons always take one arm | 0.48–0.71 ns/element | 0.52–0.63 |
| the comparisons are unpredictable | 1.01–1.10 | 0.54–0.62 |

A factor of 1.8 where the data decides the arm, and nothing where it does
not — one instruction fewer is again below the noise, and the mispredict
is again the whole of the win. Two increments in a row have now come out
this way, which is worth stating as a rule for this backend: on a wide
core the branches are what the clock sees, and the instruction counts the
cost model ranks by are a proxy that happens to point the same direction.

## Select forms, 2026-09-16

A conditional in value position is a compare and one conditional select
(`docs/spec/94-assembler.md` §9 "Select forms"). On a clamp over a span,
`total = total + (x < cap ? x | cap)`, the loop body:

```
  ldr  w5, [x0, w4, uxtw #2]        ldr  w5, [x0, w4, uxtw #2]
  cmp  w5, w2                       cmp  w5, w2
  b.hs +8                      ->   csel w9, w5, w2, lo
  b    +8                           add  w3, w3, w9
  mov  w5, w2                       add  w4, w4, #1
  add  w3, w3, w5
  add  w4, w4, #1
```

| clamp over 2^12 `u32` elements, best of seven over three runs | branch | select |
| --- | ---: | ---: |
| the comparison always takes one arm | 0.419–0.431 ns/element | 0.404–0.450 |
| the comparison is unpredictable | 1.38–1.59 | 0.395–0.420 |

Free where the branch predicts, and 3.4 times faster where it does not.
This is the first increment in this run whose win the clock sees, and the
reason is not the instruction count — six body instructions against seven
— but the mispredict: half of a 16 KiB array at a cap in the middle of
the data's range is the worst case for a predictor, and about a
nanosecond an element is what it costs. The same data through the select
runs at the speed of the loads.

Worth recording as a limit of the cost model: it counts a branch at
weight one whether or not the data decides it, so it cannot tell these
two rows apart. It priced the select form below the branch form here for
the right reason by accident — one instruction fewer — and would have
made the same choice had the arms been ten instructions and the branch
perfectly predicted.

## Multiply-add forms, 2026-09-16

An integer product and its addend are one instruction
(`docs/spec/94-assembler.md` §9 "Multiply-add forms"). The whole of the
change, on a `u32` dot product over a span:

```
  ldr   w9,  [x0,  w5, uxtw #2]        ldr   w9,  [x0,  w5, uxtw #2]
  ldr   w10, [x21, w5, uxtw #2]        ldr   w10, [x21, w5, uxtw #2]
  mul   w9,  w9, w10              ->   madd  w4,  w9, w10, w4
  add   w4,  w4, w9
  add   w5,  w5, #1                    add   w5,  w5, #1
  cmp   w5,  w1                        cmp   w5,  w1
  b.lo  loop_0                         b.lo  loop_0
```

Seven instructions an element become six, and the body stays proven —
the verifier modeled `madd`, `msub`, and `mneg` before the lowering
emitted them.

| `u32` dot product, 2^12 elements (32 KiB, L1-resident) | best of seven, five runs |
| --- | ---: |
| `mul` then `add` | 0.389–0.459 ns/element |
| `madd` | 0.425–0.458 ns/element |

No difference: the ranges overlap and neither end is reliably ahead. One
fewer instruction in a seven-instruction loop is fourteen percent of the
issue, and this core had the slot to spare — the third increment in a row
(with the reduction's remainder and the vector block loads) whose static
saving an M4 absorbs. The saving is real and it is the instruction, not
the nanosecond: it is worth the same to code size and to a core with a
narrower issue width, and worth nothing here. Recording that is the
point. The cost model counts instructions, so on this host it ranks
candidates by something the clock does not measure, and a port-pressure
or dependency-chain term is what would tell them apart.

## Map vectorization, 2026-09-16

The element-wise span maps `vectorize-maps` rewrites
(`docs/spec/94-assembler.md` §9 "Map vectorization"; `map_add.oak`,
`bench_map.c`, `run_map.sh`), measured over 2^20 elements (the byte map
over 2^22 bytes, the same 4 MB), best of seven rounds of two hundred
calls, the vectorized form as the search selects it against the scalar
loop the search keeps when the transform is withheld
(`OAK_OPT_SKIP=vectorize-maps`). Three runs on a host at load average
47–71; every row's checksum agrees, and every row is proven at the bit
level with the span memory it writes.

| Kernel | scalar loop | one vector a trip (**selected**) | speedup |
| --- | ---: | ---: | ---: |
| `add_k` — `dst[i] = a[i] + k`, `u32`, ns/element | 0.394–0.426 | 0.142–0.157 | 2.7–3.0× |
| `bump` — `v[i] = (v[i] ^ k) + 1` in place, `u32` | 0.407–0.466 | 0.123–0.127 | 3.2–3.7× |
| `fmadd_k` — `dst[i] = a[i] * k + 0.5`, `f32` | 0.365–0.432 | 0.139–0.168 | 2.5–2.8× |
| `sum_ab` — `dst[i] = a[i] + b[i]`, a zip, `u32` | 0.483–0.802 | 0.210–0.365 | 2.2–2.5× |
| `xor_mask` — `dst[i] = a[i] ^ m`, `u8`, ns/byte | 0.453 | 0.028 | 16× |

What the rows say:

- **One vector a trip is enough for a map.** The reduction needed four
  accumulators because its lanes form a loop-carried chain; a map carries
  nothing across trips, so the four-element trip already runs near the
  store bandwidth the host gives one core under this load, and the gain
  is the 2–3× the lane count and the guard elision predict together.
- **The byte map is where the lanes pay most.** Sixteen bytes a trip
  against one, and the scalar loop's per-element guard and branch are the
  same cost whatever the width: 0.45 ns a byte becomes 0.028, sixteen
  times, the whole lane count.
- **The zip is the slowest of the four word kernels either way** — three
  streams against two — and the one with the widest spread between runs,
  which is the memory system, not the code.
- **The float map vectorizes because nothing reassociates.** `fmul` and
  `fadd` round once per lane as the scalar operators do, so the license
  (`Oak.Map.blocked_eq`) needs no law of `f32` where the reduction's
  `fsum` stays scalar.

## Found on the way

- The native backend has no globals: `view(&table_high1)` of a
  package-level array is refused, so `utf8.valid` as written stays on the
  C backend. The object writer has the `adrp` relocation but not the
  page-offset `add`.
- It passes at most eight argument registers and has no stack arguments; a
  view costs two, so the literal kernel's five-view functions
  (`stdlib/literals.oak` `count`) do not lower, nor does a function with
  more than eight vector parameters.
- A `q` load indexes by bytes or by sixteens, never by a lane size in
  between, so vector loads over `u16`/`u32`/`u64` spans wait for a scaled
  index idiom.
- The verifier reports a false mismatch on a span read past its length
  (`literals.longest` with `len(starts) = 0`): the asm traps, the Oak model
  reads a fixed value. It fails a native build of any program containing
  such a function.
- A function with a `dispatch` clause lowered natively defined the
  dispatched symbol as its portable body and hid its hardware unit
  (the 23× CRC-32C row above); such functions now stay with the C backend.
- A little-endian word assembled from eight guarded byte reads at
  constant offsets is fifty-six guarded `ldrb`s in the native body and one
  `ldr` under clang; the idiom is the next CRC and hash win.
- The verifier refuted `bench_tiled` at aade7acd with a value the Oak body
  cannot produce (a negative sum of squares); reproduced there, gone at
  30ca36eb — a false alarm an upstream verifier fix closed.
