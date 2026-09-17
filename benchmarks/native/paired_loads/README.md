# Paired-load liveness: correctness and measured runtime

The shared native register helpers used to treat `ldp`/`ldpsw`'s second
destination as an input. A scalar cleanup loop's paired load consequently
kept an earlier index temporary live across the vector loop, preventing
the fourth `sum32` load from sharing the first address.

The fix aligns read sets, renaming and register reservation: both loaded
outputs remain outputs, but output/base aliases still have genuine address
reads. It also protects tied writeback bases, distinguishes vector/GPR names,
and retains conditional fallthrough in liveness. No numerical semantics,
verifier acceptance rule or optimization gate changes. The pre-existing
`TestE2ENativeVectorReduction` shape failure now passes unchanged. Execution
tests cover u32/u64 wrapping arithmetic at zero, vector-boundary and tail
lengths; helper tests cover copy propagation and address/output aliases.

## Protocol

Build `benchmarks/native/emit` at the before and after revisions, and the
`oak` CLI at the before revision, keeping those binaries outside the checkout.
No parallel compiler builds should run while timing. On ARM64 macOS:

```sh
python3 benchmarks/native/paired_loads/run.py \
  --baseline-emit /path/to/before-emit --baseline-oak /path/to/before-oak \
  --baseline-revision FULL_40_HEX_COMMIT --candidate-emit /path/to/after-emit \
  --output /tmp/paired-loads.json
```

The script checks embedded compiler revision metadata and records binary
SHA-256/build information, source/runner hashes, revision/dirty status, CPU,
compiler flags, load, selected assembly, verdicts and raw observations. Use
clean builds for recorded comparisons. `--elements` and `--samples` accept
bounded overrides; output is exclusively created and cannot overwrite a
previous report. Build directories are temporary and removed afterward.

Each run compares C (`-O3 -ffp-contract=off -fno-fast-math`), native before,
native identity, and native after. Identity disables the current registry's
transform names; all three native controls must prove both functions before
timing. Complete diagnostics include any refused candidates as well as the
selected form. Sum64 is an unchanged-assembly control for this increment.

Samples interleave all eight backend/width combinations and rotate the first
variant. Defaults are nine samples at lengths 7, 4,096 and 1,048,576, using
1,048,576, 32,768 and 128 calls per sample respectively. Full-width unsigned
inputs exercise modular wraparound. The runner checks every call against an
independent C sum; the driver also checks every sample across backends.
Volatile indirect calls prevent hoisting pure calls out of the timed loop.

Core placement, host contention and cache residency are not controlled.
Report elapsed time and its spread, including slowdowns. The smaller sum32
loop (14 → 12 instructions, still four loads) and unchanged 160-byte frame
are explanatory metrics, not evidence of a speedup by themselves.

## Measurements: 2026-09-17

Clean baseline `4d1bc1dd2ba6e46583eef65a8b4b2d82e2aca87d`; clean candidate
`7e82a813a31b0cac69288209c0cc207db4eb7fa6`. M4 Max, Apple clang 21.0.0,
nine interleaved samples of each variant, repeated with the same binaries.
All six native bodies are `proven`, and all result checks pass. Sum32 has
one address calculation instead of two and a 12-instruction main loop
instead of 14. Sum64's assembly is identical across the two compilers.
Both frames remain 160 bytes.

Primary-run medians in ns/element; positive time changes mean slower:

| Elements | Width | C | Native before | Native after | Time change | Repeat time change |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 7 | u32 | 0.5188 | 0.6785 | 0.6759 | −0.4% | +2.8% |
| 7 | u64 | 0.6082 | 0.8398 | 0.8300 | −1.2% | +1.2% |
| 4,096 | u32 | 0.0494 | 0.0461 | 0.0480 | +4.2% | −0.5% |
| 4,096 | u64 | 0.0939 | 0.0935 | 0.1023 | +9.3% | −0.6% |
| 1,048,576 | u32 | 0.0605 | 0.0576 | 0.0584 | +1.4% | +1.9% |
| 1,048,576 | u64 | 0.1155 | 0.1183 | 0.1185 | +0.1% | −7.3% |

No repeatable runtime speedup is established. The large u32 case has
slightly slower medians in both runs; this is not hidden behind its smaller
instruction count. Timings vary substantially, including for the unchanged-
assembly u64 control. One-minute host load was 38 in the first run and rose
from 61 to 75 during the repeat. These observations do not establish an
isolated-host regression guarantee or a general C-performance comparison.
This increment is an input/output correctness repair, not a claimed speedup.

The [primary report](results/paired-loads-m4-max-2026-09-17.json) and
[repeat report](results/paired-loads-repeat-m4-max-2026-09-17.json) retain all
identity controls, samples, checksums, binary provenance, assembly and
diagnostics. Nativegen/machine/opt tests, focused compiler shape/execution
tests, race checks, vet and benchmark-protocol tests pass. The original
sum-reduction shape assertion now passes unchanged; no full-suite/CI-green
claim is made.
