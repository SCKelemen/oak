# Native ARM64 host-test gate

`.github/workflows/native-arm64.yml` runs the host-dependent tests that skip on
x86 CI. It is a separate hard-failing check, named **Native ARM64 host tests**.
It does not edit branch-protection settings. A successful x86 or QEMU run does
not satisfy this check; require an actual successful hosted native run on the
candidate commit before merging.

## Scope and runner

The reviewed inventory contains 200 ARM64-host-dependent roots. Linux ARM64
executes 198 roots (193 compiler, two CLI, one assembler differential, one test
runner dispatch, and one feature-attribute regression) and 61 named children. This includes all 192 ARM-host roots
observed skipped in the former A–R shard, except the separately scoped SME test,
plus `TestVerdictCache`, the dispatch target-boundary regression, and the five
non-compiler roots.

Only two detected ARM64 roots are excluded, individually, in `EXCLUSIONS`:

* `TestE2EExampleSMEPackage`: its helper requires Darwin's SME detection via
  `sysctl` and SME-capable hardware. Linux ARM64 and SVE do not establish SME.
* `TestE2EMessageSendFoundation`: requires Darwin/ARM64 Objective-C Foundation.

These remain separate platform-coverage obligations. They are not successful
execution and are never allowed `skip` events inside the selected Linux run.
Metal/device tests and QEMU/SVE tests are also separate platform/emulator scope;
this workflow does not claim their coverage or change their checks.

The runner is the standard `ubuntu-24.04-arm` image. Three compiler shards and
one support shard run with at most two native jobs in parallel; packages within
the support shard remain serial. These are not larger/custom runners. GitHub documents this standard runner as
free in public repositories, with 4 vCPUs and 16 GB memory. No paid commitment,
repository security change, or additional runner registration is needed. Queue
availability and the actual runner image/CPU are established by the hosted run,
not by local configuration validation.

The runner's documented Cobalt 100 platform supports the features exercised by
this inventory. The workflow nevertheless logs `lscpu` and refuses an unsuitable
machine. `native_arm64_host_probe.c` checks Linux HWCAP for FP, ASIMD/NEON, CRC32
(the dispatch claim), and SHA2 (hash hardware realization), then compiles and
executes FMA, NEON, CRC and SHA2 instructions. Native atomics use base A64
load/store-exclusive loops, not an assumed LSE-only instruction set. User-mode
counter access and memory/barrier behavior remain actual assertions in the
selected tests. SVE, SME, Metal and Apple frameworks are not inferred from the
ARM64 runner label.

Official runner/toolchain and platform references, checked 2026-10-09:

* [GitHub standard hosted runners](https://docs.github.com/en/actions/reference/runners/github-hosted-runners#standard-github-hosted-runners-for-public-repositories)
* [Current Ubuntu 24.04 ARM64 image software](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Arm64-Readme.md)
* [Arm's public GitHub runner description](https://learn.arm.com/learning-paths/cross-platform/github-arm-runners/public-repos/)
* [Arm's Cobalt 100 feature inventory](https://learn.arm.com/learning-paths/servers-and-cloud-computing/azure-arm-template/verify/)

## Fail-closed coverage

1. The Go AST scanner parses test source, follows package-local helper references (including aliases, method values,
   callback tables and package-level closures),
   finds ARM64 host guards and architecture build constraints, and compares the
   resulting roots and source files with `native_arm64_inventory.json`.
2. The same manifest records every test-source `Skip`/`Skipf`/`SkipNow` call site.
   New or changed skip sites, including a differently spelled future host guard,
   require source review. This is a change detector, **not a skip allowlist**.
   The scanner is deliberately conservative and does not claim to prove arbitrary
   dynamically computed host predicates or imported helper behavior.
3. The executor requires native Linux/ARM64 host and target, CGO for `-race`, a
   real host `cc`, and the runtime ISA probe. Missing tools/host features fail.
   Once in the support shard, the feature-attribute regression compiles all four
   AArch64 catalog attributes with actual GCC and Clang, at baseline and stronger
   architectures. Both named compiler children are required; skips fail. The compiler lane also
   compiles generated baseline-to-CRC dispatch calls with GCC and Clang, at
   `-O0`, `-O1`, and `-O2`, with and without checked dispatch and baseline CRC.
   Both compiler children of that regression are required as well.
4. Each anchored exact root selector is checked against the actual Go `-list`
   inventory. Execution uses `-race -count=1`, no inherited reducing `GOFLAGS`,
   and the existing 90-minute compiler / 45-minute other-package deadlines
   (five minutes for the small feature-attribute regression).
5. The reviewed `native_arm64_shards.json` assigns every selected root exactly
   once. Required children inherit their root's shard. New/missing/duplicate roots
   or a misplaced package fail before execution.
6. Every selected root and named child must emit exactly one `run` and `pass`,
   followed by one package `pass`. Any failure, skip, missing/duplicate result,
   unexpected test, malformed JSON, or failed Go process fails the job. A parent
   test passing cannot conceal a missing or skipped child.

7. An always-run aggregate retains the **Native ARM64 host tests** check name.
   It requires every matrix child and its artifact upload to succeed, all four
   artifacts to be present, and each lane to write a success receipt only after
   its commands and checks finish. It independently rereads the raw event streams,
   exact Go commands and exit codes, rather than trusting passed-test summaries.
   Source checkout SHA, raw inventory/plan hashes, run ID, attempt and shard must
   match the aggregate's checkout. Missing, cancelled, failed, duplicate, malformed,
   truncated, mismatched or unexpected evidence fails closed.

Each native job retains the 240-minute upper bound. Compiler commands retain
90 minutes per shard; support retains its serial 5 + 45 + 45 + 45-minute package
limits. The final evidence-only aggregate has a 15-minute limit. Existing x86 race
partitions/timeouts and compatibility aggregates are unchanged. Superseded
first-attempt PR jobs cancel independently, with the shard axis in every native
concurrency key; manual reruns and non-PR jobs remain independent. Because every
artifact is bound to its run attempt, use **Re-run all jobs** for a new complete
attempt; mixing earlier successful shards with rerun-only failed shards cannot
satisfy this gate.

## Timing basis and limits of the partition

The static assignment was reviewed against run
[38001894734](https://github.com/SCKelemen/oak/actions/runs/38001894734), source
`80917e8942ae6a058fef66afe8978cd4bbd501d6`. That compiler invocation passed 90 roots
with a cumulative reported 5,008.41 seconds before the unchanged 90-minute package
deadline. The four largest completed roots were literals (1,267.85 s), C-backend
dispatch (1,117.29 s), whole-package BLAKE3 (799.70 s), and Stage2 (672.80 s).
`TestE2ENativeMapPageProvenByCases` was still running after 391.53 seconds, and
101 later roots had not run. None of those 102 roots is claimed as passing.

The three compiler shards contain 64, 65 and 64 roots respectively. The static
plan records the measured durations, the unfinished MapPage lower bound, and a
60-second planning reserve for each unmeasured root. Those estimates distribute
heavy completed roots and leave tail capacity; they are neither runtime limits
nor evidence of correctness. Future actual native execution must establish every
root and child, including MapPage and the previously unexecuted tail. Membership
is not dynamically changed by CI timings or completion order. The later
dispatch target-boundary regression is assigned to compiler-a with the same
unmeasured planning reserve; it has no measurement in the historical run.

## Local validation and maintenance

From the repository root:

```sh
go test -race -count=1 ./.github/scripts/native_arm64
python3 -m unittest discover -s .github/scripts -p 'test_native_arm64*.py' -v
python3 .github/scripts/native_arm64.py --check
```

These work on x86 and establish only the coverage gate's behavior. On native
Linux ARM64 with the required tools, a clean results directory, and the CI
identity variables (`GITHUB_SHA` equal to checkout HEAD, positive `GITHUB_RUN_ID`
and `GITHUB_RUN_ATTEMPT`), execute one explicitly selected shard:

```sh
python3 .github/scripts/native_arm64.py --run --shard compiler-a
```

The workflow preserves raw JSON event streams, exact invocation/exit records,
reviewed source inventory, identity, success receipt (only on success), and
non-authoritative passed-test summaries in one `native-arm64-RUN-ATTEMPT-SHARD`
artifact per shard, including partial streams on failure. Live resource telemetry
and each runner/ISA preflight remain in the job logs. Keep those artifacts and
logs when reporting hosted proof.

When a test/helper changes, inspect the source inventory difference first:

```sh
go run ./.github/scripts/native_arm64 > /tmp/native-arm64-inventory.json
```

Update the reviewed manifest deliberately after classifying new roots/skip
sites, then explicitly assign each new root in the static shard plan. A new ARM host test belongs in this required lane; a platform exception
needs an individual reason and a distinct coverage obligation. Add or update
exact child names when adding/removing table cases or specification-law files.
Do not auto-refresh the manifest in CI, suppress execution skips, weaken a
selector, remove `-race`, or raise timeouts to obtain a green check.
