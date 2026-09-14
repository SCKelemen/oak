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
| `crc32c` | 0.144 | 3.311 → 0.817 after the dispatch fix | 23.0 → 5.7 | trusted (indexes a package table) |
| `sha256` | 0.639 | 0.719 → 0.646 after the dispatch fix | 1.12 → 1.00 | trusted (indexes a package table) |
| `blake3` | 3.115 | 4.808 | 1.54 | trusted |
| `dot` | 0.835 | 2.704 | 3.24 | proven |
| `sum` | 0.115 | 0.393 | 3.40 | proven |
| `search` | 11.50 | 20.30 | 1.76 | proven |
| `page_probe` | 11.13 | 21.51 | 1.93 | proven |
| `bitmap` | 0.192 | 0.229 | 1.19 | C helper on both sides (noise floor) |
| `dispatch` | 10.82 | 9.03 | 0.83 | proven |
| `tiled` | — | not built | — | refuted by the verifier (see below) |

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

`bench_tiled` (an `f32` sum of squares over eight accumulators in a
`[8]f32` local, a stride-8 loop and a remainder loop) is the one kernel the
native build refuses: the verifier reports a mismatch at `len(a) = 8`,
with the asm producing `+Inf` and the Oak model `0xF66F…` — a negative
value, which a sum of squares cannot produce, and which no float
accumulator that started at zero can reach in one iteration. The lowered
asm (`results/bench_tiled-native-2026-09-14.asm`) performs the Oak body's
operations in the Oak body's order; the accumulators live in frame slots
across the two data-dependent loops, and the refutation is most likely
the verifier's model of float slots across loop summaries, not the
backend. It is recorded here as a verifier finding to reproduce in
isolation; the gate is not bypassed for a measurement (a mismatch rejects
the build, by design), so the kernel has no native row. The C backend
runs it at the speed `BENCHMARKS.md` records.

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
- The verifier refutes `bench_tiled` with a value the Oak body cannot
  produce (a negative sum of squares); a probable false alarm in the
  float-slot model across two loops, to be reduced to a unit case.
