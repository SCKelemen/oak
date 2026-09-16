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
native optimized without `vectorize-maps`, and fully optimized native code.
Each backend has f32/f64 and strict/explicit-FMA variants. Samples interleave
all sixteen combinations and rotate their starting position. The report keeps
observation order, raw elapsed times, result checksums, compiler revision,
dirty-worktree status, host/load information, native verdicts, assembly, frame
sizes, encoded sizes, and structural instruction/loop metrics. Native identity
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
