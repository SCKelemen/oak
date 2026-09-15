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
| `crc32c` | 0.144 | 3.311 → 0.817 after the dispatch fix → 0.295 with the word idiom → 0.144 with its guards elided | 23.0 → 5.7 → 1.7 → 1.1 | trusted (indexes a package table) |
| `sha256` | 0.639 | 0.719 → 0.646 after the dispatch fix | 1.12 → 1.00 | trusted (indexes a package table) |
| `blake3` | 3.115 | 4.808 | 1.54 | trusted |
| `dot` | 0.835 | 2.704 | 3.24 | proven |
| `sum` | 0.115 | 0.393 | 3.40 | proven |
| `search` | 11.50 | 20.30 → 17.2 (C 19.3 in that run) with `/ 2` as a shift | 1.76 → 0.89 | witnessed |
| `page_probe` | 11.13 | 21.51 → 21.2 (C 17.5 in that run) with `/ 2` as a shift | 1.93 → 1.21 | trusted (loop-body path budget) |
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
- **The next CRC gap was byte-wise word assembly** (fixed in this pass).
  `crc32c_chunk` reads seven little-endian words through
  `crc32c_word_at`; the native body of the chunk helper was 499 lines: 56
  `ldrb`s, each behind its own `cmp`/`b.hs` guard, shifted and or-ed into
  a word. clang turns the same source into seven unaligned `ldr`s. The
  backend now recognizes the idiom (`nativegen/wide_load.go`,
  `94-assembler.md` §9) and emits one `ldr x` per word under one slack
  guard, and the verifier reads the wide load as the bytes' concatenation
  so the bodies stay proven: the chunk helper is 177 lines with seven
  loads, and CRC-32C went from 5.7× to 1.7× (0.295 against 0.174 ns/byte
  in that run; the C side drifted from 0.144 under load). The guards went
  next: every `at` is a literal the inliner had copied into a temporary,
  leaving `len(chunk) >= t + 8`, from which the extents checker cannot
  prove `chunk[t + 3]` (the sum may wrap). The inliner now substitutes
  literal arguments (`90-backend.md` §9) and the checker folds constant
  sums, so the fifty-six accesses are proven under the caller's
  `len(chunk) >= 56` and each word is one `ldr x, [xB, #k]` with no guard:
  0.144 against 0.127 ns/byte, 1.1×, on a host at load average 300.
- **Scalar loops are not unrolled or vectorized.** `sum` lowers to the
  tight loop one would write by hand — one `ldr`, one `add`, an increment
  and two branches per element — and `dot` to the same shape with a
  multiply-add, both proven; clang at `-O3` vectorizes both. The 3.2–3.4×
  is the gap between a correct scalar loop and a SIMD one, and it is the
  price of every reduction until the backend unrolls (the register
  allocator across calls from the UTF-8 case is a separate prerequisite;
  these kernels make no calls in their loops).
- **Branchy kernels were within 2×, and the cause was a division.**
  `search` and `page_probe` are compare and branch chains over loads the
  predictor cannot help; the native code was 1.8–1.9× behind. The inner
  loop's `mid = lo + (hi - lo) / u32(2)` lowered to a `udiv` behind a zero
  check on the loop's latency chain; the strength reduction above
  (`94-assembler.md` §9.ac) lowers it to `lsr`, and a run with that
  lowering measured `search` at 0.89× and `page_probe` at 1.21× (on a host
  at load average 300, alternating the two runners; the ratios are the
  claim, not the times, and the quiet-host protocol above stands). What
  remains in `page_probe` is the guard on the fence-key and in-page loads
  the checker did not admit elided (`keys[mid * u32(512)]`, a scaled
  index, and `page[m]` inside a `subslice`). The
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
- A little-endian word assembled from eight guarded byte reads was
  fifty-six guarded `ldrb`s in the native body and one `ldr` under clang;
  the word idiom now lowers it to one load (landed), unguarded where the
  inliner's substituted literal offsets and the checker's folded constants
  prove the bytes (landed).
- The verifier refuted `bench_tiled` at aade7acd with a value the Oak body
  cannot produce (a negative sum of squares); reproduced there, gone at
  30ca36eb — a false alarm an upstream verifier fix closed.
