# Self-hosted solver performance, October 2026

This increment removes repeated work in the Oak prover and its Go twin.
The comparison baseline is `de6ffb60` on `specification`; integration also
includes the later LRAT/SAT-model proofs through `f77edc02`. Measurements
below are Linux/amd64 C-backend builds on an AMD EPYC 9V74 shared runner.
They are not ARM64/RV64 native-runtime measurements or a proof that the
whole toolchain meets its v1.0 performance goals.

## Changes

### Allocate BDD workspaces for the actual problem

The standalone shell no longer reserves three maximum-budget BDD tables
for every input file. A race starts at 4,096 nodes (or the caller's smaller
maximum), sizes its bit storage from the compacted problem's actual term
count, and allocates full tables only for applicable orders. The explicit
stack needs no more frames than the node budget, capped at 32,768.

An exhausted race retries at four times the capacity, up to the exact
original maximum. A decided or unsupported race does not retry. Each
attempt is initialized afresh, and its buffers are released before the
next one. There are no epoch counters, rollover rules, or retained stale
node identities. This deliberately keeps the existing full-clear semantics
while greatly reducing the number of entries small problems clear.

This is bounded adaptive allocation, not resumable preemption within an
expensive term. Large problems can pay for multiple attempts. The existing
certificate rung and refutation evaluator still run after the BDD race.

### Lower once for the standalone variable-order race

`lower_theorem` emits the compacted term graph and roots once.
`reorder_problem` rewrites only leaf/select variable maps. Alternate orders
copy that common problem instead of repeating symbolic evaluation,
compaction, and witness work. Interleaved, blocked, and control-first
applicability rules remain the same. The Go-hosted process protocol is
unchanged.

### Direct ternary ITE in Go and Oak

Both diagram engines now use memoized Shannon expansion over all three
operands, with terminal identities, complemented-condition normalization,
and shared output polarity. Oak uses its explicit frame stack and reuses
the existing four-word cache entries with a distinct operation tag.

The clause engine retains its certificate-producing ITE gates. Both BDD
engines change together, so their node-count agreement remains a useful
regression check. `Oak.BddComplement` proves the Boolean identities and
ternary Shannon law; it does not claim full implementation refinement of
the mutable tables.

### Resolve more write-log aliases before bit-blasting

Linear index comparison now cancels common coefficients modulo the word
width. If every remaining coefficient is divisible by `2^k` but the
constant difference is not, the indices cannot alias. Width and overflow
are part of this check; different memory snapshots remain different atoms.
No arena bounds or region-disjointness assumptions are invented.

A read scans from the newest write to find a definite overwrite or memory
marker before constructing conditional reads. It shares normal-form work
and index-pair results within that read. This avoids constructing dead
history and keeps cache lifetime tied to the actual immutable expressions.

`Oak.IndexCongruence` proves the modular arithmetic law for arbitrary sums
of divisible coefficients, including reduction by a divisible word
modulus. The Go normalizer/trailing-zero implementation is additionally
covered by exhaustive small-width and 32/64-bit boundary regressions;
that is not a claim of full implementation refinement.

### SAT decision heap and watch blockers

An indexed activity heap replaces the full variable scan. Equal activities
still choose the smallest variable id. Assigned variables are discarded
lazily; backtracking reinserts removed variables; activity bumps repair
heap order. Integer rescaling rebuilds the heap because it can create new
ties.

Each watch stores its other current watched literal. A true blocker skips
the clause-body fetch. Moving a watch also updates the opposite blocker,
so this shortcut preserves the old propagation order. An earlier
experiment allowed stale clause-member blockers; it changed search and
certificate sizes on the intrinsic corpus and was replaced by this exact
other-watch form.

Models and LRAT certificates retain their existing validation paths.

## Measurement and diagnostics

`BenchmarkOakShell` builds outside the timed region and measures fresh
processes through the whole standalone pipeline, including certificates.
`BenchmarkBDDITE` compares direct ITE with its old decomposition on the
same circuit. `BenchmarkMemoryAtOverwrite` exercises a thousand writes
whose final unconditional store answers the read.

Initial structural and memory observations:

| Workload / metric | Baseline | Updated |
| --- | ---: | ---: |
| 32 independent multiplexers, BDD nodes | 193 | 129 |
| Definite overwrite, allocations per read | 8,004 | 7 |
| Definite overwrite, allocated bytes per read | about 1,024,264 | 736 |
| Small layout theorem, BDD table entries cleared per active order | 8,388,608 | 16,384 |
| `layout.oak`, observed process peak RSS | 188,568 KiB | 107,408 KiB |

The old shell reserved about 410.7 MiB for three BDD workspaces before its
other buffers. For the layout corpus, which uses one applicable order,
the new per-theorem BDD allocation is 488–494 KB. These are allocated
capacities; RSS includes the rest of the prover and its certificate work.

Three-iteration warm-binary samples with the final other-watch policy were
about 0.529 → 0.545 seconds for `layout.oak` and 5.575 → 5.409 seconds for
`intrinsics.oak`. The final `extents.oak` sample fell from 102.455 to
52.417 seconds per run (three iterations each, certificates included).
Shared-runner timing was noisy; these samples do not
establish a general runtime speedup. The node, allocation, and table-clear
reductions are the more reproducible evidence. The overwrite microbenchmark
fell from roughly 1–4.5 ms to 1–3 microseconds on this constructed workload;
it is not a whole-compiler speedup claim.

Set `OAK_SOLVER_STATS=1` for standalone BDD comment rows:

```text
c bdd <peak BDD allocation bytes> <table entries cleared across attempts> <attempts> <winning nodes>
```

SAT's existing numeric `c` row appends three fields after conflicts,
probed variables, probe units, eliminated variables, subsumed clauses, and
strengthened clauses: decisions, watch visits, and blocker hits. These are
telemetry, not proof evidence.

Reproduce:

```sh
go test ./asm -run 'Test(BDDITE|ComplementEdge|LinearIndex|MemoryAtModular)' -count=1
go test ./asm -run '^$' -bench 'Benchmark(BDDITE|MemoryAtOverwrite)$' -count=3
go test . -run '^$' -bench '^BenchmarkOakShell$' -benchtime=3x
go test . -run '^TestOak(SolverSelfCheck|SAT|LRAT|ShellCertificates|SolverAgrees|ShellAgrees)' -timeout 25m
cd spec/lean && lake build Oak.BddComplement Oak.IndexCongruence
```

The solver self-check now exhausts two-variable ITE truth tables, compares
heap choices with a scan through backtracking/rescaling, and exercises
workspace retries, hard exhaustion, and unsupported input. It also fixes
an existing LRAT fixture whose declared proof length was two words too
large. Previously the resulting failure bit 256 became exit status zero
on Unix; all failures now produce exit status one and print their mask.

## Remaining performance work

Fine-grained resumable BDD scheduling and cancellation of individual
losing jobs in the Go-hosted process batch remain separate work. So do
verified facts about arena-region bounds/disjointness and classification
of ARM64/RV64 optimization refusals against hardware benchmarks. The
changes here do not relax any proof acceptance requirement or claim to
complete those larger workstreams.
