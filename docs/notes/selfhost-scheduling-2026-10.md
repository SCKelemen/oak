# Resumable BDD races and batch cancellation

Follow-up to the allocation, ITE, alias, and SAT work in PR #661.

## Scheduling

Multi-order standalone races now rotate after at most 4,096 explicit BDD
stack transitions, with a separate bound of 4,096 term visits. Apply, ITE,
and restriction retain their stack pointer, frame contents, and partial
result across quanta. The unique table, operation cache, node numbering,
and completed term bits stay in place.

Bit-vector operations reconstruct their local scaffold using a per-term
tape of completed primitive results. Replayed calls do not touch the live
stack or rebuild nodes. The first unfinished call resumes its stack;
calls after a pause are inert. Only a fully completed term publishes its
bits and advances the term cursor. This preserves the original operation
order and exact node counts, including quantified and arithmetic terms.

The tape is bounded to 32,768 words (128 KiB) per active scheduled order.
Overflow reports exhaustion, never a proof. A single applicable order uses
the ordinary path and allocates no tape. A zero quantum does no work;
completed, unsupported, exhausted, and cancelled continuations are stable.
Node-budget growth still restarts at the next capacity, as before.

The quantum bounds stack transitions and term visits, not wall-clock
latency or individual hash probes. Reconstructing a term can replay its
bounded prefix. Lowering, exhaustive enumeration, and certificate checking
are not made resumable by this change.

## Cancellation

The Go batch retains one persistent process per variable-order slot.
A private one-byte-per-theorem file is inherited read-only on descriptor
3. Once the existing arbitration rules settle a theorem, the parent sets
that theorem's byte. Workers skip settled theorems before lowering and
poll during BDD execution every 4,096 transitions/term visits. A cancelled
BDD returns the distinct non-verdict status 9, never partially built roots.

Each theorem's output is flushed immediately, so the parent can release
losing workers before the complete batch ends. The next theorem reuses
the worker and starts with fresh solver state. Source parsing and work
already inside lowering/enumeration can finish before cancellation is
observed. Cancellation-file read failures merely leave work running.

Selecting a race result is not proof admission. Oak-lowered results retain
priority; a held Go-lowered result cannot cancel Oak orders prematurely.
Existing replay, witness, certificate, and model checks remain at their
admission sites. Duplicate output from one slot cannot stand in for other
orders. Context cancellation and partial-startup errors kill/reap children;
reader goroutines stop even when their output channel is full.

## Validation

- Compiled self-checks compare every published bit and exact node counts
  against uninterrupted runs at quanta 1, 2, 7, and 127. Cases include
  arithmetic, ITE, restriction, refutation, unsupported input, exhaustion,
  zero work, and cancellation. A two-order race checks that a cheap order
  wins while the expensive first order is still below its budget.
- Full Go/Oak solver and standalone-shell corpus comparisons pass.
- SAT/model/corruption, LRAT, and shell-certificate regressions pass.
- Actual Oak execution checks the inherited bitmap. Process fixtures check
  per-theorem progress, result preference, duplicate replies, and context
  cleanup. The process fixtures also pass under Go's race detector.
- `Oak.SolverScheduling` proves abstract quantum composition, invariant
  preservation, and stable finished/cancelled states. These are scheduling
  laws, not a refinement proof of the mutable Oak stack and replay tape.
- The full Lean build passes after rebasing onto the upstream SAT-model
  soundness repairs and native/Wasm proof updates (304 jobs).

The prior compiler CI fixture passed `ys` simultaneously as a writable
span and read-only view. That fixture was independently repaired upstream
while this change was being validated; this branch retains the upstream
repair. The broader compiler CI timeout is not claimed resolved here.

## Measurements

Measurements compare PR #661 (`9102507c`) with this change on Linux amd64,
Go 1.27.1, using prebuilt test binaries and cached solver executables.
Shell timings include certificate checking. The synthetic alternating-order
benchmark uses eight 16-bit addition-commutativity jobs, alternating which
slot gets a good or bad variable ordering. It isolates batch head-of-line
blocking and is not an application-wide speedup claim.

| Workload / metric | #661 baseline | Updated |
| --- | ---: | ---: |
| Alternating-order batch median, 20 runs | 88.4 ms | 35.5 ms |
| Alternating-order batch p95, 20 runs | 117.6 ms | 63.5 ms |
| Alternating-order total CPU, 20-run process including harness | 1.73 s | 0.87 s |
| Alternating-order process-tree maximum RSS | 28,900 KiB | 28,848 KiB |
| Layout median, three samples of three iterations | 270 ms | 256 ms |
| Intrinsics median, three samples of three iterations | 3.573 s | 3.642 s |
| Extents, one iteration | 35.20 s | 43.81 s |
| Extents process-tree CPU, including harness | 34.60 s | 35.50 s |
| Extents process-tree maximum RSS | 269,840 KiB | 270,152 KiB |

These shared-host samples show substantially less wasted batch work, not
uniformly faster theorem solving. The extents wall-time sample regressed
while CPU increased about 3%; one sample cannot distinguish scheduling
noise from a repeatable latency change. RSS is the maximum reported by
`wait4` across the process tree, not the sum of simultaneously resident
workers. Native ARM64/RV64 hardware performance was not measured.

Reproduce:

```sh
go test . -run '^Test(OakSolverSelfCheck|OakCancellationBitmap|SolverCancels|SolverCancellation|SolverContext)' -count=1
go test . -race -run '^TestSolver(Cancels|Cancellation|Context)' -count=1
go test . -run '^$' -bench '^BenchmarkOakAlternatingOrders$' -benchtime=1x -count=20
go test . -run '^$' -bench '^BenchmarkOakShell$' -benchtime=3x
cd spec/lean && lake build
```
