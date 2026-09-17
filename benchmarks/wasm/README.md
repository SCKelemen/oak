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

Counter, sum, swap and GCD modules also shrink by 61–63 bytes and 34 Wasm
instructions each. The code-size difference includes section-length LEB changes.
Broader loop shapes still use the dispatcher; formal source-to-Wasm translation
verification, general structurization, local reuse and stackification remain open.

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

Choice, guarded-division and arithmetic-join fixtures lose 68 bytes and 39 Wasm
instructions each. The complete timed module shrinks from 327 to 258 bytes;
its code-size delta also includes a body-length LEB change. The tests retain
untaken traps, short-circuit evaluation, Unit calls and merge computations;
neither faster execution nor smaller bytes grant a formal translation verdict.

## Acyclic forward CFGs

`compiler/wasm_forward_test.go` retains dispatcher bytes from `65477201` for
nested/sequential conditionals and a loop calling a nested conditional helper.
The caller loop is structured in both versions. Static fixture gates show
253→167 bytes for the nested function, 248→160 for the sequential function,
and 421→335 for the complete kernel. Each loses 48 Wasm instructions.

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

`compiler/wasm_region_loop_test.go` retains dispatcher bytes from `bd89ea49`
and compares them with v7 region-loop lowering. Conditional and nested-body
modules shrink 342→251 and 436→312 bytes; instruction counts fall 144→93 and
191→122. Normal tests execute both versions against independent wrapping-u32
oracles and cover zero trips and boundary values.

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
