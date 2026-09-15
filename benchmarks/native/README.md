# The native backend against the C backend

The question this harness answers: when the same Oak function is emitted
by the native backend (the Oak assembler alone, `oak build -native`;
`docs/spec/94-assembler.md` §9) instead of the C backend (clang over the
emitted C), how far behind is it, and why? The OS pilot is moving to the
native backend, so this is the gap that decides whether the golden-case
results hold there.

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
rounds, 1 MiB per kernel, and the checksums agree on every row.

Apple M4 Max, Apple clang 21.0.0, 2026-09-14, revision aade7acd. The host
was loaded (load average 35–40 from another session's test suites), so
the ratios are the measurement, not the absolute times; `bitmap`, which
is the same C-realized helper (`arm64.cnt64`) on both sides, bounds the
noise at about twenty percent. Raw samples:
`results/kernels-m4-max-2026-09-14.jsonl`.

| Kernel | C backend ns/byte | Native ns/byte | Native / C | Verdict on the native body |
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
