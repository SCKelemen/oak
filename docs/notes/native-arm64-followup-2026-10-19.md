# Native ARM64 follow-up, 2026-10-19

Checked PR #737 head `eeeb267b9b4bcc19e90a32801ca20b640a7ba1ae`.
The specification base is `93d501026ef134f3788f27aedcdfacfb2e608a19`.

## Ordinary check failure

The packages job (117008579590), standard-library job (117008579076), and
typed-CNF supplied-instance job (117008576138) all panic in
`TestTypedCNFAdversarial/read-mixed-value-width`. The retained typed-CNF
artifact's `runs/normal/stage.log` confirms the same panic; this is not a Lean
failure or a resource-owner failure.

Commit `12e48e09` correctly made the producer reject conflicting memory widths.
The negative replay fixture still asked that producer to construct an invalid
formula, so its setup panicked before testing the independent replay checker.

The repair first produces a valid same-width snapshot, then corrupts one read
and its memo-root width. A fresh producer must refuse the corrupted claim and
latch exhaustion. Independently, replay of the forged snapshot must still
reject it with its exact-span/32-bit domain check. Truncating the forged memo
only bypasses the earlier shape rejection in this adversarial test; no
production guard, proof condition, or runtime source changes.

The original focused test reproduced the panic locally. The corrected full
`TestTypedCNF*` and `TestBlastMemoryWidth*` groups passed both normally and with
the race detector using Go 1.27.1 on Linux/amd64. This does not replace the
hosted typed-CNF Lean generation/checking workflow.

## Native timeout remains open

Run [38911613189](https://github.com/SCKelemen/oak/actions/runs/38911613189)
passed all three compiler shards. Support job 117008578365 again exhausted
the shared 90-minute prerequisite budget in `native-prover-build`, exit -9,
`timed_out=True`. The root runtime was not run and the strict aggregate failed.
The source inventory still lists 1,086 eligible functions. The late telemetry
has completed search 235 (`count_candidates`) and entered `failure_rows`.
This is continuing cumulative work, not evidence of one stuck call.

The successful scalar-text diagnostic took about 472.6 seconds with all three
expected candidate validations. Its race-enabled CPU profile contains 1,203.26
CPU seconds; `__tsan_read`, `racecall`, and `racecalladdr` together account for
about half of sampled CPU. These samples identify instrumentation cost in this
specific workload, not permission to remove race checking or a demonstrated
whole-build optimization.

The separate BDD lookup ABBA diagnostic passed its semantic controls and
reported identical semantic counters in its measured workloads. It failed
strict allocation parity: one baseline Add32 sample reported 26 allocations
and 2,528,424 bytes; the other three samples reported 25 and 2,528,408. Add32
and Add64 timings overlap and do not show a consistent benefit. The bounded
memo workload improved in both pairs, but that alone does not justify adopting
the candidate as a full-build fix. The diagnostic's comparison remains a
failure; no parity condition is relaxed.

The native prerequisite, final aggregate, and complete ordinary checks remain
mandatory on the eventual final revision. No merge is justified by this test
repair or these partial profiles.
