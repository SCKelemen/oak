# Constant-table views: proof-gated lookup performance

This benchmark extracts the exact `grapheme_table` and `grapheme_class`
definitions from `stdlib/grapheme.oak`; no hand-optimized lookup replaces
the Oak source. The input has 1,631 ranges, each stored as three u32 words.

The verifier previously rejected a local `table: []u32 = view(&grapheme_table)`.
It already modeled direct table reads and table arguments to calls. Local
views now reuse that same symbolic root, element contract and exact length.
On the measured ARM64 lookup this makes the existing gated machine candidate
eligible: 49 → 45 instructions overall, 14 → 12 in the loop, frame unchanged
at 80 bytes. Its verdict changes from trusted to inductively proven. No
source semantics, proof budgets, search policy or transform gates change.

The same change corrects a verifier length bug: `len(subslice(table, 1, 2))`
must be 2, not the whole table's length. Positive and deliberately incorrect
machine bodies test length, root, offset and signed reads; ARM64 and RV64
checker/verifier tests cover the alias path. Unknown/shadowed sources,
mutable constructors and mutable-global-only roots remain outside this new
subset. Native ARM64 tests cover execution and the actual stdlib lookup proof.
The smaller four-entry lookup execution fixture does not yet prove its loop;
no general table-loop coverage or universal implementation-refinement claim
is made.

## Protocol

Keep clean before/after emitter binaries and the before Oak CLI outside the
checkout. On ARM64 macOS, with no compiler/test builds running:

```sh
python3 benchmarks/native/table_views/run.py \
  --baseline-emit /path/to/before-emit --baseline-oak /path/to/before-oak \
  --baseline-revision FULL_40_HEX_COMMIT --candidate-emit /path/to/after-emit \
  --output /tmp/table-views.json
```

The four controls are C (`-O3 -ffp-contract=off -fno-fast-math`), native before,
native identity (all registered transforms disabled), and native after. The
after candidate must prove; every native verdict and selected body is recorded.
The script checks embedded compiler revisions and records binary hashes/build
metadata, fixture and runner hashes, flags, host load and raw timings. Output
uses exclusive creation. Temporary generated sources and executables are scoped
to a temporary directory and removed afterward.

Each distribution has 4,096 deterministic inputs: ASCII, uniform Unicode code
points, or range-boundary neighbors. All include zero, 0x110000 and UINT32_MAX.
An independent linear scan computes expected outputs outside timing. Every
timed lookup is checked, and every sample's checksum must match all backends.
Volatile indirect calls prevent call hoisting. Nine samples of 256 rounds
(1,048,576 lookups each) are interleaved across all backend/distribution pairs,
rotating the first pair each round.

Core placement, cache residency and host contention are uncontrolled. Static
instruction counts are not a runtime result. Interpret timings with their
spread and repeat them; do not infer a workload-wide win from this one lookup.

## Measurements: 2026-09-17

Clean baseline `efb4a203f2dc448121e4b8f1d616593bf4acde84`; clean candidate
`8a4e223b7b101ae1396e1b7a0eef8ebac7b97c60`, M4 Max, Apple clang 21.0.0.
Two complete nine-sample runs used the same frozen binaries. All oracle and
cross-backend checksum checks passed. Native identity and native after were
proven; native before retained its explicitly trusted fallback.

Medians in ns/lookup; negative changes mean less elapsed time:

| Distribution | C | Native before | Native identity | Native after | Time change | Repeat time change |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ASCII | 24.26 | 33.69 | 49.27 | 30.86 | −8.4% | −14.8% |
| Unicode | 20.42 | 28.93 | 43.14 | 27.09 | −6.4% | −8.6% |
| Boundaries | 24.02 | 33.93 | 48.69 | 30.54 | −10.0% | −13.2% |

The repeat's before/after medians were 39.46/33.62, 31.74/29.01 and
36.55/31.72 ns respectively. Both runs show lower median time for every
distribution. Native still takes about 1.27–1.33× the C time in the first
run: this does not establish parity with C or a whole-program improvement.

Host contention is substantial: one-minute load fell from 153 to 146 in
the first run and 141 to 119 in the repeat. Distributions overlap and the
repeat has large outliers (for example, Unicode native-after ranges from
25.44 to 76.77 ns). These are observed host-specific gains, not a controlled
regression guarantee. An earlier dirty-binary three-sample probe, concurrent
with compiler/test work at load above 230, was too noisy for a speed claim
and is not used in this table. No compiler/test builds were launched during
the two recorded timing runs.

The [primary report](results/table-views-m4-max-2026-09-17.json) and
[repeat report](results/table-views-repeat-m4-max-2026-09-17.json) retain all
raw samples, verdicts, selected assembly and provenance. Focused verifier and
compiler tests, their race checks, nativegen/MachineIR/optimizer suites, vet
and benchmark-harness tests pass; the full repository suite was not run.

## Exact extent folding: 2026-09-17

This is a separate before/after comparison, not an update to the historical
table above. Clean baseline `d735d322aa483cff5a4f91caf8d641fd1a437a82` versus
clean candidate `eec594520f2b1c49702fdee11a03b49703874a96` on the same M4 Max,
using the unchanged protocol, fixture, runner and C flags. Both reports retain
all nine samples per backend/distribution and the exact binary provenance.

The shared native recognizer folds u32 `len(named_view) / constant` and
`% constant` only when the recorded view extent agrees with its owned-array
or table extent. It does not fold dynamic spans, subslices, effectful
expressions, nested conversions or zero divisors. It uses the existing
`Strength` candidate, with no new default switch or verifier relaxation.
RV64 retains emitter reductions after source rewriting, as ARM64 already did.

For this lookup, `4893 / 3` becomes `1631`. That also allows the existing
checker-fact guard elimination to remove the remaining in-loop bounds check.
The selected body drops from **43 to 38 instructions**, its loop from **12 to
10**; the 80-byte frame and five load/store instructions are unchanged. Counts
are emitted instructions, excluding bind/clobber/frame directives. Before,
identity and after are all inductively proven; all independent oracle and
cross-backend checksum checks pass. These counts explain the candidate, not
its wall-clock profitability.

Medians in ns/lookup:

| Distribution | C | Native before | Native identity | Native after | Change | Repeat before / after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ASCII | 34.95 | 41.44 | 71.46 | 38.14 | −8.0% | 61.62 / 38.61 |
| Unicode | 38.33 | 34.13 | 57.55 | 32.49 | −4.8% | 38.09 / 34.47 |
| Boundaries | 32.16 | 43.08 | 66.98 | 40.33 | −6.4% | 41.44 / 40.65 |

Every distribution's median decreases in both runs, but this host is **not
quiet**. One-minute load rose from 154 to 156 in the first run and 176 to 187
in the repeat, with other compiler/test jobs active (including our broader
RV64 test command). The repeat changes vary from −37.3% for ASCII to −1.9%
for boundaries, and timing ranges overlap substantially. The first run's C
Unicode median is itself distorted enough to appear slower than native.
These measurements are directionally encouraging, **not a reliable speedup
estimate, C-parity claim or regression gate**. Repeat on a quiet host before
using them as such; no throughput claim is made for RV64.

The [first report](results/extent-fold-m4-max-2026-09-17.json) and
[repeat report](results/extent-fold-repeat-m4-max-2026-09-17.json) include the
raw samples and exact selected bodies. Both-lane unit tests require proof of
quotient/remainder bodies and composition with source rewrites. ARM64
end-to-end tests check native/C results, retained zero-divisor/subslice traps
and the actual grapheme candidate's proof and division-free assembly.

Validation: nativegen, MachineIR and optimizer suites, focused compiler and
materialization tests, targeted race checks, vet and harness tests pass.
RV64 source-rewrite, strength, span-local and subslice cross-target tests pass
with a writable temporary Zig cache. The broader RV64/QEMU sweep did **not**
complete: its ten-minute suite deadline expired while linking the ADT
record-ABI fixture through Zig (`runNativeRV64BareWith`, before that QEMU
invocation). It is not counted as a passing suite; the full repository suite
was not run. The isolated record/ADT ABI test subsequently passed both
subtests through QEMU with the temporary cache (48.82 seconds), within its
separate three-minute deadline.
