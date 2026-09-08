# JSON decoder optimization measurements

Measured candidate: `e9b0201226b2ce69b54ab60ae2a191ff1c910fe8`.
Baseline: `bb8932260e444d56f2d009fdefcde16ddbdcd0e4`.
[Paired workflow and raw sample artifacts](https://github.com/SCKelemen/oak/actions/runs/34284042286).
Machine-readable summaries: [optimization-2026-09-08.json](optimization-2026-09-08.json).

| Runner | Oak baseline ns/document | Oak candidate ns/document | Raw speedup | simdjson candidate ns/document | Oak / simdjson time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Apple M1 (Virtual) | 819.34 | 438.53 | 1.87× | 120.59 | 3.64× |
| AMD EPYC 9V74 80-Core Processor | 835.21 | 491.85 | 1.70× | 122.10 | 4.03× |

These are median timings from five samples of 1,024,000 documents per
backend, using the fixed required-field integer/Bool/array schema in
schema.oak. Both paths consume and validate all fields and check their
materialized output against independent expected values before timing.
Sanitizer runs passed on both architectures. Release compilation uses
-O3 -DNDEBUG without LTO. Exact compiler/host metadata and every timing
sample are retained in the workflow artifacts.

The candidate removes repeated integer scans, replaces per-digit division
with a checked cutoff, avoids full array-element token lookahead, handles
ASCII keys without Unicode decoding, splits punctuation from the large
scanner, and adds bounded SIMD ASCII UTF-8 validation. All changes apply
to ordinary derived decoders, not a benchmark-only parser.

The Linux simdjson control changed by approximately +0.02%, supporting a
real Oak improvement in this run. The M1 control improved by approximately
17.5% between baseline and candidate processes: the raw 1.87× M1 speedup
cannot all be attributed to Oak's code. Relative to its simdjson control,
Oak's M1 improvement is approximately 1.54×; this normalization is a noise
indicator, not a statistical correction or confidence interval. Runners
are virtualized, core affinity and frequency are uncontrolled, and the
baseline process runs first.

Oak remains slower than simdjson on this schema. These results do not
establish optimality, general JSON parity, or language-wide superiority.
Remaining targets include generated helper call/copy costs, scalar numeric
accumulation, linear schema dispatch, and the separate validation pass.
Profiling and emitted-code inspection should select the next change;
additional schemas and dedicated M-series hardware are needed before
broader claims. Allocation counts are not instrumented.
