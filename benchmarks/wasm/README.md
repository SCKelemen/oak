# Experimental Wasm performance

Record guest execution separately from compiler payload/startup, Oak compilation,
engine instantiation, and browser UI latency. Static Wasm instruction counts are
not native JIT instruction counts. Test results do not grant formal verification.

## Four-block structured loops

The first runtime comparison uses checked-in pre-change dispatcher bytes, not a
second mode of the current compiler. Source, byte fixtures, reference results and
timing harness live in `compiler/wasm_loop_test.go`. Normal CI gates exact sizes
and execution results; the timing test is opt-in:

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmStructuredLoopTiming$' -count=3 -v
```

Use `node` instead of `deno` to select Node explicitly. Each test launches a fresh
engine, instantiates both final modules, warms both, then alternates their order
for seven timed samples. Each sample makes eight sum calls with roughly one
million iterations per call and checks the wrapping-u32 results. Compilation,
instantiation and warmup are excluded. There is no noisy elapsed-time CI gate.

[2026-09-17 raw samples](structured-loop-2026-09-17.json) show ratios of median
structured/dispatcher execution time between 0.151 and 0.436 across four local
engine processes. This is encouraging but preliminary: the Darwin/arm64 shared
host was noisy, its CPU model probe was unavailable, and only one small kernel
was timed under Deno 2.9.6 / V8 15.0.245.2-rusty. It is not evidence of the same
gain in Chrome, other Wasm engines or representative applications.

With recipe-v9 stack expressions, counter, sum, swap and GCD now shrink
87–117 bytes and 38–52 Wasm instructions relative to their retained dispatcher
baselines. The code-size difference includes section-length LEB changes.
Nested reducible source loops now use the structured-region path below. Raw
unmatched/irreducible CFGs still use the dispatcher; formal source-to-Wasm
translation verification, general structurization and broader local reuse remain
open. The recorded structured-loop timings predate stack expressions and isolate
that earlier control-flow increment.

## Four-block conditionals

`compiler/wasm_branch_test.go` retains pre-change bytes from `b95bdffb`. The timed
kernel sums calls to a parity-based conditional helper. Its caller already uses
structured loop lowering in both versions: this comparison isolates replacing
the helper's dispatcher with direct `if/else` and a shared join.

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmDiamondTiming$' -count=3 -v
```

It uses the same warmup, alternating ordering, seven samples and eight calls of
roughly one million iterations as the loop test. Both versions are checked
against wrapping-u32 reference results. [Raw samples](diamond-2026-09-17.json)
retain all four local processes: the initially noisy run had a ratio of medians
of 0.073, while three repeats gave 0.134–0.136. These are Deno/V8 microbenchmark
observations on a shared Darwin/arm64 host, not a general speedup guarantee.

The simple-choice fixture remains 133→65 bytes/55→16 instructions; recipe-v9
stack expressions take guarded division to 68 bytes/16 instructions, the
arithmetic join to 71/20, and the complete kernel from 327 to 161 bytes and
127 to 56 instructions. The historical timing record isolates the earlier
diamond increment. The tests retain
untaken traps, short-circuit evaluation, Unit calls and merge computations;
neither faster execution nor smaller bytes grant a formal translation verdict.

## Acyclic forward CFGs

`compiler/wasm_forward_test.go` retains dispatcher bytes from `65477201` for
nested/sequential conditionals and a loop calling a nested conditional helper.
The caller loop is structured in both versions. Recipe-v9 static fixture gates
show 253→129 bytes for the nested function, 248→130 for the sequential
function, and 421→214 for the complete kernel; instruction counts fall
114→54, 112→54 and 174→86. The recorded timing samples isolate the earlier
forward-control increment.

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmForwardTiming$' -count=3 -v
```

The timing protocol is unchanged: fresh engine per test, both lanes warmed,
seven alternating samples, eight calls of approximately one million iterations
per sample, results checked against a wrapping-u32 oracle. Compilation and
instantiation are excluded. [All three local samples](forward-cfg-2026-09-17.json)
show median new/old ratios of 0.387–0.438. This remains a small Deno/V8 kernel on
a shared Darwin/arm64 host, not a Chrome measurement or application-wide claim.
Normal CI checks exact bytes/instructions and execution, not elapsed time.

Generated CFG tests cover another 2,304 input pairs across 64 graphs, including
shared joins and early returns. Depth-limit, lazy trapping calls, Unit results,
signed overflow and Bool guards are tested separately. The extension remains
untrusted lowering with independent byte validation, not formal source-to-bytes
verification.

## Pre-test loops with acyclic bodies

`compiler/wasm_region_loop_test.go` retains dispatcher bytes from `bd89ea49`.
With recipe-v9 stack expressions, conditional and nested-body modules shrink
342→153 and 436→192 bytes; instruction counts fall 144→61 and 191→82.
Normal tests execute both versions against independent wrapping-u32 oracles and
cover zero trips and boundary values. The recorded timing samples isolate the
earlier v7 region-loop control lowering.

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmRegionLoopTiming$' -count=3 -v
```

The nested-body benchmark uses the same fresh-process, dual-lane warmup, seven
alternating samples and eight roughly one-million-iteration calls. Compilation
and instantiation are excluded; every result is checked. Six local processes
gave median region-loop/dispatcher ratios from 0.021 to 0.121. Several individual
samples were extreme outliers in both lanes, so this evidence only says that the
dispatcher was consistently slower for this kernel on this Deno/V8 setup. It is
not a stable speedup estimate, a Chrome result or a timing CI gate. [Raw samples](region-loop-2026-09-17.json)
retain every observation.

Raw-CFG tests additionally cover multiple latches, loop exit edges, early
returns, shuffled block storage, inverted header polarity and the 124/125-block
depth boundary. Effect tests cover lazy trapping calls, Unit results, entry/
header/exit operations, signed overflow, zero-trip bodies and nested-loop
dispatcher fallback. None grants formal source-to-Wasm equivalence.

## Nested structured regions

`compiler/wasm_nested_loop_test.go` compares the unchanged public raw-CFG
dispatcher route with production lowering supplied both checked structured OptIR
and its exact CFG. Nested counters shrink 337→203 bytes and 140→66 instructions;
adding a conditional inner body shrinks 437→255 bytes and 189→88 instructions.
Normal tests execute both lanes against independent nested-loop references and
cover calls, lazy division traps, Unit results, zero trips and Bool guards.

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmNestedLoopTiming$' -count=3 -v
```

The opt-in benchmark uses the conditional inner body, a fresh engine per test,
15 warmup batches per lane, seven alternating samples and four calls at `n=1000`
per sample. Compilation and instantiation are excluded and every result is
checked. [All three local samples](nested-loop-2026-09-17.json) have median
structured/dispatcher ratios of 0.087–0.100 under Deno 2.9.6 / V8
15.0.245.2-rusty. This small quadratic-loop microbenchmark on a shared
Darwin/arm64 host is not a stable speedup estimate, Chrome result, representative
application result, timing CI gate or formal proof.

## Pure single-use stack expressions

`compiler/wasm_stack_test.go` retains production recipe-v8 bytes from
`5185645c` and compares them with recipe v9. The candidate emits total, pure,
single-use same-block SSA trees directly at their use and removes the resulting
locals. The complete loop/conditional-helper module shrinks 258→161 bytes and
88→56 Wasm instructions. Normal tests independently execute both lanes on
ordinary and large inputs and final candidate bytes pass the separate validator.

```sh
OAK_REQUIRE_WASM_TESTS=1 OAK_WASM_TEST_ENGINE=deno OAK_WASM_BENCHMARKS=1 \
  go test ./compiler -run '^TestWasmStackExpressionTiming$' -count=3 -v
```

The longer timing protocol uses a fresh engine per test, twenty warmup batches,
seven alternating samples and eight calls of roughly ten million iterations.
[All three raw runs](stack-expression-2026-09-18.json) had extreme outliers in
both lanes; ratios of medians ranged from 0.884 to 1.519. This does not establish
a runtime improvement. The deterministic module/instruction reduction is the
result; elapsed time remains an observation rather than a gate.
