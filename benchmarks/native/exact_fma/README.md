# Measured FMA: reductions and independent maps

Run from the repository root on an ARM64 macOS host:

```sh
go run ./benchmarks/native/exact_fma -workload dot -out /tmp/dot.json
go run ./benchmarks/native/exact_fma -workload map -out /tmp/map.json
```

The output path must not already exist. Defaults are 4,096 elements,
4,096 calls per sample, and nine samples of each variant. `-n`, `-calls`,
`-samples`, and `-cc` override these settings within checked bounds.

Every run compares C (`-O3 -ffp-contract=off -fno-fast-math`), native identity,
native optimized without `vectorize-maps`, native with only one vector per map
trip (`unroll-vector-maps` disabled), and fully optimized native code.
Each backend has f32/f64 and strict/explicit-FMA variants. Samples interleave
all twenty combinations and rotate their starting position. The report keeps
observation order, raw elapsed times, result checksums, compiler revision,
dirty-worktree status, host/load information, native verdicts, assembly, frame
sizes, encoded sizes, rewrite licenses, and structural instruction/loop metrics. Native identity
disables the registry's actual transform names rather than a hard-coded list.
Temporary builds are removed; the report is retained. Volatile indirect calls
prevent C from hoisting identical pure calls out of the timed loop.

## What is being compared

`dot` converts bytes explicitly to f32 or f64 before multiplication and keeps
one sequential accumulator. Every product is an integer at most 65,025, hence
exactly representable in either format. Contraction is mathematically exact
for this input family, but this harness does not add a production contraction
license or an IEEE implementation-refinement theorem. Native verdicts judge
each function against its own source; they do **not** prove the two sources
equivalent. In the initial experiment the strict native loops were only
witness-checked, with their continue-condition proof undecided. That limitation
is recorded, not promoted to `proven` by matching benchmark outputs.

`map` computes independent output elements. Its fused source already calls
`fma`: vectorizing that intrinsic preserves one rounding per lane, using the
existing `Oak.Map.blocked_eq` schema and SIMD FMA semantics. The matcher
requires the checker's builtin width and recursively lane-wise arguments.
It does not infer an error budget, reassociate reductions, contract ordinary
multiply/add, or assume a user function named `fma` is the builtin. The source
tail remains scalar. The initial implementation targets ARM64 performance;
RV64 uses the same matcher when vector maps are enabled, but no RV64 timing
claim is made.

Map timing inputs are small exactly represented multiples of 0.25, with
`k=1.25` and `c=0.5`, so strict and fused checksums also agree on this dataset.
The general map API does not promise strict and fused expressions agree.
Separate compiler execution tests use cancellation-sensitive values, signed
zeros, subnormals, infinities and NaNs, f32/f64, nested FMA, zip arguments, and
zero/short/vector/tail lengths. Non-NaN results are checked bitwise; NaNs by
classification, not unspecified payload identity. Shadowed/effectful calls
are refused, and strict multiplication/addition must remain two operations.

## Acceptance

A shorter instruction sequence is not sufficient. Compare elapsed time with
the same-current-compiler no-map baseline before enabling a rewrite. The dot
experiment found safe contraction slower on this M4 Max, so no automatic
contraction was enabled. Independent FMA maps showed a substantial SIMD gain
and retained proven native verdicts. Both experiments remain reproducible here.
Core placement and machine contention are uncontrolled; use the raw samples
and load metadata when interpreting ratios. C comparison is retained even
when Oak improves: beating the previous native form is not parity with C.

## Two-vector map candidate

`unroll-vector-maps` adds a two-vector main loop before the existing
one-vector cleanup and scalar tail. It instantiates `Oak.Map.grouped_eq`:
two consecutive blocks map the same elements with the same lane operations.
`grouped_bounds` proves the extent/next-index inequalities, including the
no-wrap case with a u32 limit. These are schema proofs; the matcher and
lowering remain implementation code, and emitted candidates must still pass
the ordinary seam checker and semantic verifier.

The single-vector cleanup matters: inputs between one and two vectors must
not become all-scalar. A conditional cleanup was also tried; its joins made
several maps harder to prove. The retained loop form proves f32/f64 FMA,
nested/zip expressions, strict arithmetic, and unsigned integer maps without
changing verifier rules. Sharing the second vector's index in a generated
local was refused by the existing seam checker and was not retained.

The cost model now recognizes a smaller-stride cleanup, not just a scalar
remainder. An 8-element main loop followed by 4-element cleanup and a scalar
tail has cost hints of at most one cleanup trip and three scalar trips.
`MaxTrips` counts trips, so a bounded loop is no longer divided by its stride
twice. These are cost hints, not proof evidence. Materialization revision v8
includes the grouping flag; metric/cost artifacts advance to v2.

Use `native-one-vector` as the control for this increment. Original reports
below predate this extra control and retain their original four-backend
protocol. Compare small/tail-heavy inputs separately: wider loop setup and
code size can cost time even when long maps improve. No automatic float
contraction or reduction regrouping is introduced.

## Recorded results: M4 Max, 2026-09-17

Clean revision `1ef944b1537ec1dbad9653ff42f7068f7415c669`, Apple clang
21.0.0, default 4,096 elements × 4,096 calls, nine interleaved samples per
variant. Dates here are local (Europe/Stockholm); reports use UTC. Entries
are median ns/element, not best times. The host was heavily loaded:
one-minute load averages 78.40–79.69 during dot and 75.91–72.47 during map.
These are observed kernel improvements, not a quiet-host regression gate
or a claim about other workloads or machines.

### Independent explicit-FMA maps

| Width | C | Native identity | Native without maps | Native optimized | Speedup over no-map control | Native / C |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| f32 | 0.0591 | 0.5596 | 0.3855 | 0.1134 | 3.40× | 1.92× |
| f64 | 0.1455 | 0.5767 | 0.3861 | 0.2276 | 1.70× | 1.56× |

Every native map body, including the strict controls, has a `proven`
verdict. The scalar FMA body is 76 encoded bytes; its vectorized form is
156 bytes, including the scalar remainder. This is a runtime win with a
code-size cost, not an instruction-count-only result. All sample checksums
agree. Native still trails C; that remaining gap must not disappear from
the performance record. Full timing distributions, strict-map controls,
assembly and verdicts are in the [raw map report](results/map-m4-max-2026-09-17.json).

### Sequential byte dot products: contraction rejected

| Width | C strict | C explicit FMA | Native optimized strict | Native optimized explicit FMA | Native FMA / strict |
| --- | ---: | ---: | ---: | ---: | ---: |
| f32 | 0.9331 | 1.6208 | 1.0355 | 1.3772 | 1.33× |
| f64 | 0.9809 | 1.5376 | 1.0481 | 1.4322 | 1.37× |

Contraction makes this sequential loop slower despite reducing optimized
body size from 120 to 116 bytes. The generated fused loop carries its
accumulator through `fmadd`, whereas the strict loop carries it through
`fadd` after an independent `fmul`; the result is consistent with a
loop-carried dependency cost, not a measurement of instruction latency.
There is no map here: the no-map and optimized controls have identical
assembly, and their timing variation illustrates the host noise.

Strict native dot bodies remain `witness-checked`, not proven; explicit
FMA bodies are proven against their own source. Checksum agreement does
not upgrade those verdicts or establish a general contraction license.
Full results, including identity and no-map controls, are in the
[raw dot report](results/dot-m4-max-2026-09-17.json).
