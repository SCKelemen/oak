# Implication stage attribution evaluation

This change adds bounded diagnostic attribution to the existing exclusive implication wall-time metric. Twelve obligation classes identify existing semantic callers. Six coordinator stages distinguish DAG admission, explicit canonicalization, recursive scheduling, the joined BDD race, attempted standalone pruning, and other work. Solver verdicts, proof allowances, cache authority, worker implementations and cancellation/join obligations are preserved.

Joined BDD time is wall time for the complete coordinator operation, including admission, cancellation, cleanup and joining. It is not summed worker CPU time. Standalone pruning records an attempted coordinator call, including possible admission refusal. Coverage is limited to instrumented wrappers; direct compatibility entries can make completeness false. The output retains the current candidate and its dominant class, not a history of all candidates or proof operands. Interpret stage totals only with the completeness and saturation fields.

## Validation and source composition

The isolated candidate was based on `9f46989c810743d4dbb8dbcefd566ad2e928c61c`. Its source manifest SHA-256 is `6b8fb7777172e29eab80230f8b5e9fb16d6411a93addf1781ff8bebb1f6ef3eb`. Selected normal tests passed 509 root/child identities; selected race tests passed 84. These are finite selected suites, not package-wide race or whole-compiler acceptance. The final handoff SHA-256 is `34eecaa93ea5643ac2ba44733640f5acb6a2e500ac6d315aca468ced9b220002`. Earlier failed attempts remain retained in that handoff.

This evaluation publication preserves the seven accepted production and portable-test files exactly and composes them onto `fb8fe0f817562fdaacd0b7eb9c78067204f48e81`, preserving its reader extraction/refinement integration. All affected old blobs match the tested candidate base. The local binaries also contained a diagnostic benchmark declaration. That file is excluded here because it intentionally requires `-benchtime=1x` and rejects normal benchmark calibration. No retained production or portable-test source references its declarations. This exact portable combined tree has not been rebuilt locally; current-head hosted CI must validate it. The existing packages job selects both portable test files with unfiltered `go test -v -race`.

## Measured observation cost

The retained standalone screen used `-test.v -test.run=^$ -test.bench=^BenchmarkImplicationAttributionFixed160000$ -test.benchtime=1x -test.count=1`. It ran four tiny routes in disabled/enabled AB and BA order: sixteen batches of 10,000 calls, 160,000 calls total. Setup is outside each batch timer; per-call budget copying and semantic guards are included in both modes. Terms are reused. Allocation counters are process-wide. This is a coarse warm screen, not a cold native-producer workload or a statistically powered performance comparison.

| Route | Added ns/call, AB | Added ns/call, BA | Added allocations/call, AB / BA |
| --- | ---: | ---: | ---: |
| Equality | 442.368 | 466.990 | 2.000300 / 2.000200 |
| Memo | 586.678 | 349.495 | 2.000300 / 2.000100 |
| Canonicalization | 1094.709 | 1376.868 | 2.000200 / 2.000200 |
| Recursive | 5303.333 | 1140.555 | 4.000600 / 4.000100 |

The recursive paired-order spread was 4162.778 ns/call. No predeclared coarse trigger fired: pair thresholds were 25,000 ns/call and 8 allocations/call, with a 5,000 ns/call order-spread threshold and rounding uncertainty checked. That result does not establish low overhead, negligible overhead, a native speedup or producer feasibility. The scaffolding-inclusive benchmark ns/op summary is not per-wrapper cost.

The raw 4,523-byte screen log has SHA-256 `e0f18a8c2ee56ea5b77530acc6d562633544606cc9c3589f3cf72f1c2761d5ec`; its 6,057-byte measurement report has SHA-256 `cca4520c38dabb192015908e9c1c8ab5757df07f5bd2960ff4014972061e8e42`. The excluded benchmark source has SHA-256 `c5d4f34979164a6abd709f80f2240a4b37ab143976456773d86b82ea0be5f495`. These identify retained evaluation evidence, not additional repository test obligations.

## Bounds and remaining acceptance

The fixed per-session slab is 22,432 bytes on the measured 64-bit layout. Each existing live scope grows by 40 bytes, including non-implication scopes. This is not a global memory/RSS cap. The ordinary serial five-scope compiler chain adds 200 bytes on that path; retained closures and arbitrary reentrant/concurrent hooks do not gain a global lifetime bound from this observation.

Eight owner slots, 64 frames per slot and 4,194,304 session events are bounded. Cap retirement, stale ownership, missing context, unsupported classification and saturation make completeness sticky. Dropped-event counts are a lower bound after retirement. Existing 5-second sampling, 1,202-record, 8,192-byte row and 4 MiB output caps remain. The 2,048-byte extension supports the documented 45-minute worst-width forecast, not a 90-minute worst-width completeness guarantee. Output limiting remains explicit.

Native ARM64 production remained blocked by the producer timeout before this change. The new telemetry is intended to identify the expensive coordinator stages in a fresh run; it does not fix that timeout or prove any native root or law. Merge still requires all required checks and explicit disposition of performance findings, including the earlier verifier-options cold-component result. Generated-reader refinement remains limited to the extracted Lean semantics; extractor correctness and the emitted-machine-code chain remain open.
