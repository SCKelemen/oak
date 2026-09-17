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
