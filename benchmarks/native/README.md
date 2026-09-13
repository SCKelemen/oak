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
