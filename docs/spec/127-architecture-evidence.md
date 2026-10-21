# Architecture baselines and CI evidence

`proof-obligations.json` is the deterministic inventory of **CI job obligations**
and Lean sources. Generate/check it with:

```sh
python3 -m pip install PyYAML==6.0.3
python3 benchmarks/architecture/ledger.py --write
python3 benchmarks/architecture/ledger.py
python3 -m unittest discover -s benchmarks/architecture -p 'test_*.py'
```

The ledger retains every workflow's event filters, job dependencies, conditions,
runner selection, matrix, steps, exact commands, requirement environment flags,
and continue-on-error settings. Each workflow and non-hidden Lean source under
`spec/lean` and `spec/lean-sail` has a SHA-256. An obligation's address is its
workflow path plus job key; matrix cases and step indices refine that address.
The architecture-evidence job rejects drift, including removed workflows or
changed proof sources. Regenerate and review the diff when either changes.
This is an explicit inventory, not a lock preventing deliberate gate removal.

A listed source is **not a discharged proof**. The ledger does not parse Lean,
resolve imports, enumerate declarations, or certify absence of axioms/sorry.
It does not map every theorem to a test or imply unconditionally executed CI
coverage. Read conditions and required-backend scripts alongside the ledger.
Existing theorem trust audits and ARM64/RV64 gates remain authoritative and
unchanged in obligation scope. See `126-verification-chain.md` for refinement
limits and `125-verification.md` for proof semantics.

## Reproducing measurements

`benchmarks/architecture/measure.py` executes an argv command without a shell,
keeps its exit status, and writes JSON even for ordinary command failure.
Linux with Python `os.wait4` is required. Example from repository root:

```sh
python3 benchmarks/architecture/measure.py --output /tmp/build.json --cache-state unspecified -- go build -o /tmp/oak .
```

Records include revision, worktree state, command, cwd, UTC start, host platform,
architecture, CPU count, toolchain versions, CI run/attempt/job identity, wall
and CPU seconds, and maximum RSS in KiB. RSS is Linux wait4's maximum child RSS,
**not summed concurrent process-tree memory**. Tool discovery precedes timing;
installation/download time is excluded unless performed by the measured command.
A failed sample is diagnostic evidence, never a successful performance baseline.
External termination before JSON is written can leave no artifact; CI fails
missing artifact uploads rather than inventing a sample.

The `Architecture evidence` workflow downloads Go modules, disables setup-go
cache restoration, and uses a dedicated build cache for cold/warm Go builds.
The formal workflow measures the existing RV64 proof batch and full Lean build,
without removing targets or changing failure behavior. Those runs are marked
`unspecified` cache state because earlier proof work can warm dependencies.
Artifacts `architecture-go-build` and `architecture-lean-build` belong to the
exact GitHub run and attempt; a PR run can measure a synthetic merge revision,
which is recorded rather than substituted with the PR head.

These are initial observations, not performance gates. Compare several samples
on the same runner class, toolchain, command, and cache policy before claiming a
regression. No universal threshold or fabricated historical baseline is supplied.

## Remaining evidence gaps

- Per-theorem obligations, assumption closure, and implementation correspondence
  need a Lean-aware exported ledger; lexical source inventory cannot supply them.
- Native ARM64 host and emulated RV64 runtime performance need separate hardware
  baselines. Existing execution gates are recorded, not replaced by x86 timings.
- Per-job elapsed time and executed/skipped test coverage require GitHub run and
  test-result ingestion; static workflow coverage is not execution evidence.
- Peak aggregate memory, cgroup limits, hardware model, loaded-host noise,
  repeated distributions, and controlled cold Lean builds remain future work.
- External model/source provenance stays in the existing pinned model workflows
  and audit scripts; this inventory does not independently verify that provenance.
