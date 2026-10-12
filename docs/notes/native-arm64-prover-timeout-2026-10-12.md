# Native ARM64 prover prerequisite investigation, 2026-10-12

## Failure and current state

PR #737's head `26f63158d44a0c87728489cbc899041a7dcde42a` triggered
run [38264057966](https://github.com/SCKelemen/oak/actions/runs/38264057966).
Support job 114861610876 checked out the synthetic merge
`441b8ace4e0aa72687c586900107200c9f09e27f`, not the head tree alone.
The root race harness built and listed its tests; native-prover-build then used
5373.242 seconds against its remaining 5372.727-second deadline. Exit -9 was
recorded with timed_out=true by the process-group deadline owner. Linking and
root runtime execution were not reached. The strict aggregate correctly failed.

The newer head `12ac2f6883a5e85eb01627ec2036d6d81e4c91b9` already includes
session-options capture, checked-CNF ownership, implication timing, and a
measurement note. Those changes were reused, not reimplemented. Its
[run 38301734262](https://github.com/SCKelemen/oak/actions/runs/38301734262)
also failed support (job 114986016672), with all three compiler shards passing
and the other reported workflows successful. The prerequisite again exhausted
its deadline: 5374.076 seconds against 5373.511 seconds remaining.

## What the artifacts establish

Both source inventories contain 1086 eligible functions. At the last recorded
sample, both compilers had started search 235 (`count_candidates`) and completed
234. An unsuccessful candidate search is not itself the final build verdict:
the report and allowed fallback rules still govern the completed build.

The original run's 182 resource samples record zero OOM kills, zero swap use,
maximum process-tree RSS 7,052,910,592 bytes, and minimum MemAvailable
8,681,132,032 bytes. This does not measure CPU contention, but gives no evidence
of memory exhaustion or swap pressure. The process was explicitly deadline-killed.

In the newer run's last sample (5220 seconds after observer start), exclusive
implication time was 2806.016 seconds, validation outside its nested phases
1039.499 seconds, and search outside validation 739.444 seconds. 29,866 of
29,867 implication calls had finished. This is cumulative verifier/optimizer
cost, not evidence of a single stuck implication. Samples stop before the
90-minute deadline; they do not establish the exact final operation at death.
Raw stage status and last timing records are retained in the adjacent
`native-arm64-prover-timeout-2026-10-12/hosted-summary.json`.

## Targeted optimization

A bounded 120-second, non-race Linux/amd64 CPU profile of the public compiler
checking the artifact's exact prover sources for Linux/ARM64 found 45.21% of
sampled CPU cumulatively in unique-table and operation-memo growth (17.07% and
28.14%). Multiplication bit-blasting was a major caller. This local segment
reached `mk`, search 33; it is not an end-to-end profile of the hosted timeout.

Both tables doubled repeatedly while rehashing every occupied entry. The patch
skips an intermediate doubling when the existing admission-sized final capacity
allows it. It retains exact key comparison, node IDs, insertion order, the
half-full threshold, the operation-memo eviction limit, and cancellation checks.
No BDD decision, proof rule, candidate, native test, timeout, or budget is removed.

The unique table derives its ceiling from the **live** node allowance at growth,
because implication owners lower budgets after blaster construction. Allocation
is still lazy, after admission. Final capacity is unchanged. Old/new table
overlap remains within the existing 1.5-times-final-capacity estimate; this is
still an estimate, not a guarantee about RSS or race-shadow memory. Intermediate
capacity can be larger earlier in a proof, which requires hosted measurement.

## Reproduction and limits

The adjacent `profile-probe.go.txt` is the exact bounded diagnostic driver.
Copy it into a temporary directory inside the repository module, build it with
Go 1.27.1, and pass the artifact's `native-prover/source` directory and an output
CPU-profile path. It targets ARM64 but runs the Go compiler on the host. Exit 2
means the deliberately bounded profile stopped with compilation incomplete.
Use `go tool pprof -top <binary> <profile>` for CPU attribution. No performance
number from this driver establishes native machine-code execution, race coverage,
a successful producer receipt, or full-prover completion.

## Validation

Baseline profile: source head `12ac2f68`; candidate profile: that head plus
this patch. Linux/amd64, Go 1.27.1, eight-CPU quota; neither profile uses `-race`.
The initial focused BDD tests pass. The two bounded profiles each reached
search 33 / candidate 3, with 1580 candidates considered, 1578 materialized,
37 completed validations, and 35 validations in completed searches. Cumulative
completed-validation time was 95.703 seconds before and 87.722 seconds after
(an 8.3% reduction in this one local pair). This is not a controlled repeated
whole-build speedup estimate: the profiles stop mid-proof, later implication
counts differ, and racing variable orders are sensitive to scheduling. Both
builds remained incomplete. The retained logs contain the bounded driver's
final diagnostic line as well as timing JSON records.

The 600,000-entry table benchmark (three samples, ten iterations each) reduces
allocated bytes from approximately 66,060,300 to 55,574,600 per operation
(15.9%), and allocations from six to four. Median times were 77.11 ms and
71.10 ms, but samples overlap substantially (61.11–87.03 versus 62.92–75.33 ms).
Treat the allocation reduction as established for this fixture and the timing
as descriptive, not a reliable whole-build prediction. The benchmark's two
policies run in groups, not a randomized interleaved experiment.

`go test -race -count=1 ./asm -run
'^Test(BDD|Complement|PostExhaustion|ImplicationTiming|UnsignedSuccessor)'`
passed (2.682 seconds test execution). This includes exact-table lookup,
canonical BDD truth tables, eviction/recomputation, cancellation/joining,
resource admission, refusal after exhaustion, and proof/refutation controls.
The enhanced unique-table rehash cancellation and live-budget growth tests also
pass under `-race` after the final test edit.

`python3 -m unittest discover -s .github/scripts -p 'test_native_arm64*.py'`
ran 100 tests: 97 passed; three process-group tests errored when this execution
environment could not read child `/proc/<pid>/stat` entries. The affected tests
are successful-producer late-evidence prevention, orphan-held stdout deadline,
and successful-leader descendant cleanup. These are unchanged script tests;
none was disabled or converted to a skip. The local suite is **not green** and
hosted execution of all 100 remains required. Raw output is retained alongside
this note.

## Required before merging #737 into specification

Run all four native shards together on the final PR head/current merge tree and
one workflow attempt. Support must finish the original cold race-harness prover
prerequisite within the same shared 90-minute budget, validate all bound source,
recipe, supplied-unit and native report evidence, then execute the root law
comparisons and remaining support tests. The existing strict aggregate must
accept all current-attempt artifacts and every required root/child. All ordinary
PR checks must also pass on that final head. Neither earlier compiler-shard
passes nor these local cross-target tests substitute for hosted verification.

This is a measured optimization candidate for an identified cost, not a claim
that the entire prerequisite now fits its deadline. If it still fails, retain
its implication timings and resource samples and profile a later expensive
function before making another change. Do not raise limits or allow silent skips.
