# JSON decoder optimization measurements

## Second optimization pass

Measured candidate: `8e5951dab25bd75c21f0b4be7fe3fc59313314ec`.
Baseline: `01f4ca73cc737b15c7bf5f0a237a0cdbff3b56a2` (includes the first optimization pass below).
[Paired workflow, raw samples, generated C and assembly](https://github.com/SCKelemen/oak/actions/runs/34287768558).
Machine-readable summaries: [schema-optimization-2026-09-08.json](schema-optimization-2026-09-08.json).

| Runner | Oak baseline ns/document | Oak candidate ns/document | Raw speedup | simdjson ns/document | Oak / simdjson time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Apple M1 (Virtual) | 458.71 | 265.01 | 1.73× | 132.96 | 1.99× |
| INTEL(R) XEON(R) PLATINUM 8573C | 378.63 | 165.96 | 2.28× | 96.61 | 1.72× |

The candidate specializes bounded literal record keys, removes repeated
lookahead scans, checks required punctuation directly, accumulates the first
19 integer digits without overflow bookkeeping, and passes a compact internal
integer scan value. These changes apply to ordinary derived decoders. The
public Result API, exact error categories, bounds checks, escaped-key semantics,
and complete root UTF-8 validation remain intact. No boxing or heap allocation
was added; runtime allocation counts are still not instrumented.

The emitted ARM64 scanner returns its 16-byte value in registers. Its i32
wrapper's stack frame decreased from 64 to 32 bytes relative to the initial
inspection. This confirms a specific ABI improvement, not elimination of all
aggregate copies or stack storage. Assembly and generated C are retained with
the measurements through the harness's --inspect option.

Both native sanitizer preflights and release checks passed. Focused JSON tests,
including truncation, escaped duplicates, numeric differential tests, nullable
records and fixed arrays, passed. The compiler/standard-library full race suite
was still running when this report was prepared; no full-suite pass is claimed.

Five samples each process 1,024,000 documents/backend with the unchanged
integer/Bool/four-element-array schema. simdjson remains pinned to
f5de14f09256982933af2849beb43778bd421ca7 (v4.6.11); flags remain -O3 -DNDEBUG,
without LTO. Both paths validate and materialize all fields, then consume the
same checksum. Corpus preparation and parser allocation are outside timing.

The M1 simdjson control improved by 6.44% between baseline and candidate
processes; the raw 1.73× Oak speedup includes that noise. Relative to the
control, the improvement is approximately 1.62×. The Linux control improved
by 1.45%. These are noise indicators, not statistical corrections. Intermediate
pre-compact-layout measurements also showed improvements: M1 time ratios
2.26× and 2.26×, Linux ratios 1.63× and 1.61× in workflows
[34287379682](https://github.com/SCKelemen/oak/actions/runs/34287379682) and
[34287499276](https://github.com/SCKelemen/oak/actions/runs/34287499276).
Linux used different CPU models across jobs; do not attribute cross-job raw
latency differences solely to code changes.

The final M1 ratio is about 2× simdjson's decode time on this one small typed
workload. This establishes useful proximity, not equivalent speed or general
JSON parity. Hosted virtual CPUs have uncontrolled affinity/frequency; large
strings, floats, larger arrays, selective extraction and streaming-sized inputs
still need separate measurements. Field lookup remains linear, digit processing
scalar, and UTF-8 validation a separate pass.

## First optimization pass

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
