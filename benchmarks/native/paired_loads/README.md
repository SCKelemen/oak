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
