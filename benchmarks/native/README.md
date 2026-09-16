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
proven at the bit level. What remains is the slot traffic of the five
vector locals the register file did not hold (the flattened kernel's live
set peaks past the twenty homes; the liveness allocator of program item 2)
and the loop's scalar bookkeeping.

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
