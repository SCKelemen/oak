# JSON decoder optimization measurements

## Fourth optimization pass: the reader's shape

Measured candidate: `35ae143e48e9edfb3da61be9a9f8fc828c1584a4` (branch `sam/json-decoder`, rebased on `223df157`).
Baseline: `223df15790c9314af06140f7f30c830f0dbecb53`.
Machine-readable data: [reader-shape-baseline-2026-09-12.json](reader-shape-baseline-2026-09-12.json),
[reader-shape-candidate-2026-09-12.json](reader-shape-candidate-2026-09-12.json).
Run locally (GitHub Actions quota exhausted): `python3 benchmarks/json/run.py --samples 9`,
Apple M4 Max, clang `-O3 -DNDEBUG`, simdjson at the checkout's revision, the machine
otherwise idle; each sample decodes 102,400 documents (9,096,600 bytes) per backend.

| Run | Oak ns/document | simdjson ns/document | Oak / simdjson time (medians) | Paired-ratio median |
| --- | ---: | ---: | ---: | ---: |
| Baseline | 75.50 | 63.03 | 1.198× | 1.219× |
| Candidate | 64.48 | 64.60 | 0.998× | 1.003× |

Paired ratios, baseline: 1.504, 1.094, 1.337, 1.219, 1.224, 1.227, 1.207, 1.177, 1.211.
Candidate: 1.057, 0.835, 1.107, 0.947, 1.001, 1.003, 1.003, 0.998, 1.009. The first
sample of each run carries warm-up; the simdjson control moved 2.5% between runs.
Affinity, frequency and thermal state remain uncontrolled; a hand-written decoder for
this schema with the same acceptance rules measures 47 ns per document on the same
harness, so the derived reader is at simdjson and not yet at the ceiling.

What changed (`docs/spec/71-codecs.md` §20): integer and Boolean fields decode in
place through the compact scanner instead of the per-type reader's `Result` round
trip; the opening brace and bracket are one byte after whitespace; array elements
scan from the lookahead position; the scanner takes every word of digits, counting
the run at a word's front with no branch and no count-trailing-zeros instruction
(`Oak.JsonDigits` bit-blasts the mask soundness, the run count, the eight-digit value
and the seven partial-word values); an escaped key is decoded once and compared as
bytes; `json_skip_space` and `json_scan_integer` no longer assert on the hot path;
`json_space` decides the common case with one comparison; the backend forces the
scanner, its word arithmetic, whitespace skipping, the boundary test and the
decoded-key comparison inline. Public error categories, the per-type reader API and
the acceptance rules are unchanged; the preflight of invalid inputs and the checksum
are the harness's own.


## Third optimization pass: M1 proximity target

Measured candidate: `c5debc11f324838c286c96c0c237f48c16824f3d`.
Baseline: `661e614e8da9ab49e46d23a11f788492fb256766` (includes the second pass below).
[Workflow, raw samples and native code](https://github.com/SCKelemen/oak/actions/runs/34290861422).
Machine-readable data: [word-optimization-2026-09-08.json](word-optimization-2026-09-08.json).

| Runner | Oak baseline ns/document | Oak candidate ns/document | Raw speedup | simdjson ns/document | Oak / simdjson time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Apple M1 (Virtual) | 207.37 | 119.91 | 1.73× | 105.87 | 1.133× |
| AMD EPYC 7763 64-Core Processor | 195.15 | 178.67 | 1.09× | 127.58 | 1.400× |

The M1 ratio of median times is 13.3% above simdjson, within the requested
10–20% range for this workload and run. Nine samples each process 1,024,000
documents/backend. The schema, corpus, validation policy, checksum, simdjson
revision and release flags are unchanged. Corpus/parser setup stays outside
timing; complete validated typed materialization stays inside timing.

This is not a guarantee that every sample or JSON workload falls within 20%.
The M1 paired sample ratios are 1.265, 1.129, 1.665, 1.121, 1.138, 1.409, 1.172, 0.935, 1.033.
Their range is 0.935–1.665×. The simdjson median control changed by
1.34%; affinity, CPU frequency and virtualization remain uncontrolled.
The Linux result is 40.0% above simdjson and does not meet the M1 target.
Do not use cross-run CPU-model changes as evidence of a code speedup.

Earlier candidates are retained rather than selecting only the best run:

| Candidate / workflow | M1 time ratio | Notes |
| --- | ---: | --- |
| [5305f740](https://github.com/SCKelemen/oak/actions/runs/34289575827) | 1.482× | Separate key fallback; word key expressions; whitespace loop |
| [00e36f7f](https://github.com/SCKelemen/oak/actions/runs/34289690619) | 1.327× | Eight-digit arithmetic |
| [60a24e75](https://github.com/SCKelemen/oak/actions/runs/34289844608) | 1.379× | Direct Boolean reader; test fixture needed borrow-scope repair |
| [3372d108](https://github.com/SCKelemen/oak/actions/runs/34290092315) | 1.252× | Compiler coalesces complete byte packs |
| [8fd893af](https://github.com/SCKelemen/oak/actions/runs/34290240398) | 1.139× | Overflow-safe helper guard and packed-load regressions |
| [022ab3c1](https://github.com/SCKelemen/oak/actions/runs/34290499350) | 1.184× | Successful-parse UTF-8 validity; mutation fixture needed a name fix |
| [d2050140](https://github.com/SCKelemen/oak/actions/runs/34290654967) | 1.212× | Corrected mutation fixture, paired-ratio reporting |
| Final candidate above | 1.133× | Packed Boolean spellings; one array lookahead; nine samples |

Changes apply to ordinary derived decoders and general byte-pack expressions.
The scanner batches eight validated digits using word arithmetic; codegen
coalesces complete 4/8-byte packs into one checked portable helper. ARM64
assembly confirms a single 64-bit load for an eight-byte batch. Keeping key
fallback storage separate reduced the inspected record reader frame from
304 to 208 bytes. Boolean matching and array lookahead avoid unnecessary work.
No boxing or heap allocation was introduced; allocation counts remain
uninstrumented.

Successful parsing of the supported typed grammar establishes UTF-8 validity:
ASCII values/delimiters and validated key spellings cover every consumed byte.
Failures still run whole-input validation to preserve InvalidEncoding
precedence. Unicode/escape matching and public Result APIs remain unchanged.
See the [codec specification](../../docs/spec/71-codecs.md) for the argument
and the constraints on extending this optimization to future field types.

Both native sanitizer and release preflights passed. The focused JSON suites,
byte-pack alignment/trap checks, byte-lane differential checks, encoding
mutation tests, borrow-boundary checks and golden corpus passed. The final
full compiler/standard-library race suite was still pending/running when this
report was prepared; no final full-suite pass is claimed.

Dedicated M-series hardware, additional schemas, long strings, floats, larger
arrays and streaming-sized working sets remain necessary for broader claims.

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
