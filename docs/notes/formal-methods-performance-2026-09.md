# Note: the most performant formal-methods implementation — what the codecs, os, ml, simdjson and Futhark teach the prover

**Status: in progress — benchmarks, the first enumeration increment, resident runner workers, the BDD tables and the id-indexed witness evaluator landed.** 2026-09-12, `specification` branch.
Source: a read of Oak's own verification engines (`prove/`, `asm/`,
`repl/leancheck.go`, `testrunner/`, `experiments/verification-poc`), of
`github.com/SCKelemen/os` and `github.com/SCKelemen/ml` for techniques those
repositories *measured*, and of the simdjson/simdutf structure and the
Futhark compiler's flattening and fusion ideas, against the method the
codec and UTF-8 tracks followed (`71-codecs.md` §17–§21, `70-strings.md`
§8): find the fastest structure on today's hardware, prove it, make it the
simplest thing the user writes.

The question asked was whether those techniques make the *verification*
side — the prover, the bit-blaster, the liveness checker, the Lean
exchange, the test runner — as fast as the code it verifies. This note
records what the engines do today, what the neighbouring repositories
actually measured, and the increments in leverage order, each with its
measurement and its proof obligation.

## 1. Baselines

Go benchmarks now pin them (`prove/bench_test.go`, `asm/bench_test.go`,
`testrunner/bench_test.go`; run with `go test ./prove ./asm ./testrunner
-run xxx -bench . -benchtime=1x`). This machine, load average 14–20,
`-benchtime=1x`:

| Benchmark | Wall | Reported |
| --- | ---: | --- |
| `BenchmarkTheoremsLattice` | 3.78 s | 31 decided, largest BDD 1,482,423 nodes |
| `BenchmarkTheoremsEffects` | 2.54 s | 14 decided, largest BDD 950,634 nodes |
| `BenchmarkTheoremsPatterns` | 0.84 s | 15 decided, largest BDD 3,287 nodes |
| `BenchmarkTheoremsProtocols` | 19.98 s | 7 decided (liveness exploration through the interpreter) |
| `BenchmarkBDDAdd32` / `Add64` | 0.74 ms / 2.57 ms | 4,595 / 18,403 nodes; 6.2 / 7.2 M nodes/s |
| `BenchmarkBDDMul8` / `Mul12` | 3.2 ms / 372 ms | 21,338 / 1,133,955 nodes; 6.6 / 3.0 M nodes/s |
| `BenchmarkCampaign` | 32.1 s for 2,000 cases | 62 cases/s |

Earlier command-line timings (`oak prove spec/oak/lattice.oak` 5.71 s,
`effects.oak` 3.19 s, `patterns.oak` 0.97 s, load 30–60) include model
construction and the Lean projection; the benchmarks time the deciders.

Two of these numbers reorder the plan below: the liveness exploration of
`protocols.oak` at twenty seconds is the largest single cost in the
repository's own specification, and the test runner at sixty-two cases a
second — a process and a temporary file per case — is three orders of
magnitude from what a compiled property test costs to run. Items 7 and 9
therefore come right after the benchmarks, before the BDD engine, whose
throughput of six to seven million nodes a second through Go maps is the
next largest.

## 2. What the engines do today (file:line, `specification` at fbc9b1f8)

**The prover ladder** (`prove/prove.go:84`) decides theorems one after
another. Refinement domains are enumerated through the interpreter
(`domainSize` :131, `valuesOf` :219): every value is a heap-allocated
`object.Object`, a record is a `map[string]object.Object` per tuple
(:294–299), and the odometer loop (:358–385) applies the theorem through
`evaluator.Apply` with a map-based environment per case. `loopHeavy`
(:391) stringifies the AST and substring-searches for `while`.

**The bit-blaster** (`asm/verify.go`, `asm/blast.go`, `asm/bdd.go`)
builds terms without hash-consing (`verify.go:266`); the witness pass
allocates a `map[string]uint64` and a `map[*term]uint64` per evaluation
(:295–306, :3739). The ROBDD is textbook: ripple-carry adders
(`blast.go:361`), shift-and-add multiplication (:499), quadratic popcount
(:576) and count-leading-zeros (:593), a memo keyed on the `*term`
pointer (:195–210), a two-million-node budget (:58), grouped variable
order (:90). `bdd.go` keeps the unique table and the operation cache in
Go maps (`map[bddKey]int`, `map[bddOpKey]int`, :29–30), computes `not` as
an exclusive-or with true (:71) and `ite` as three applies and a `not`
(:145); there are no complement edges, no garbage collection, no
reordering.

**Liveness** (`prove/liveness.go`) explores states by breadth-first
search through the interpreter per (state, step), with string canonical
keys (:475), Tarjan over maps (:399) and linear edge scans (:322–339).

**The Lean exchange**: `prove_cmd.go:75` runs `EmitLeanRoots` once per
theorem, so N theorems cost N+1 full compilations; `repl/leancheck.go:60`
shells out to `lake env lean --json` per check.

**The test runner** (`testrunner/native.go:303–320`) forks a process and
writes a temporary text report per case, with `Workers: 1` by default.

**SAT** exists only in `experiments/verification-poc`: an external
CaDiCaL, an in-repo LRAT checker, and a naive RUP without watched
literals.

## 3. What the neighbours measured, and what is only an idea

Measured in `ml`: a structural plan cache keyed on the shape of the
computation (`ml/schedule/schedule.oak:141–210`); capture and replay of a
decided plan (design log 0016: 97 to 419 tokens per second); work
proportional to the *enabled* set rather than the declared one; static
`u32`-handle arenas instead of pointers (`ml/graph/graph.oak`);
recompute-versus-materialize decided by a heuristic the Lean license
theorem bounds; an extraction-drift gate (`ml/scripts/check.sh`); the
oracle in the same language and differential fuzzing that straddles the
thresholds (`ml/fuzz/fuzz.oak`); worst-first roofline sweeps
(`ml/bench/sweep.py`).

Measured in `os`: TLA+ symmetry sets and state constraints (used by only
2 of 33 specs, `os/spec/tla/IPC.tla`); mutation-tested checkers with
bounded shrink counts; protocol-derived generators
(`os/pilots/oak/simulation/rendezvous_protocol_test.oak`); bit-packed
model state (`os/pilots/oak/simulation/model.oak`); scalar bitset, pool,
quotient-filter and static-filter collections (`os/lib/collections/src`);
the benchmark-validity and parity-gate disciplines.

Ideas only (no measurement in either repository): every SIMD technique
(`movemask`, table lookups, prefix-xor; bit-parallel NFA and shuffle DFA),
horizontal fusion, autotuned variants, memory planning, Bloom or
binary-fuse prefilters for visited sets. Neither repository contains SAT
or BDD work; those lessons come from the literature and from what the
codec track showed about Oak's own hot loops (proven loads, no
per-element allocation, one pass that hands positions to independent
work).

## 4. The plan, in leverage order

Each item names the structure, the measurement that decides it, and the
proof obligation that keeps the engine sound. Nothing lands without all
three. With the baselines in hand the order of execution is 1, 7, 9, 2,
3, 5, 6, 4, 8, 10; the numbering below is kept as first written.

1. **Benchmarks first.** `prove/`: `BenchmarkProveLattice`, `Effects`,
   `Patterns` over the three files above; `asm/`: `BenchmarkBlast` over the
   term shapes the lattice file produces (the 1.48-million-node case
   pinned by name); `prove/liveness`: the largest pilot model;
   `testrunner`: a hundred trivial cases. Recorded in a `RESULTS.md`
   beside them, paired with the baseline like the codec runs.

2. **The BDD engine's tables** (the largest measured cost: 1.48 million
   nodes through Go maps). Structure-of-arrays node storage (`lo`, `hi`,
   `var` as flat slices, `int32` ids), an open-addressed unique table and
   operation cache keyed on packed `uint64`s, complement edges so `not` is
   free and each function has one canonical node, a native `ite` (one
   recursion instead of three applies), and a generation-stamped cache
   so a cleared cache is one counter bump. This is the os collections
   lesson (scalar, static, u32 handles) applied where the profile says
   the time goes. Measurement: nodes per second and wall on the lattice
   file. Proof: the canonicity invariant (`lo ≠ hi`, ordered variables,
   one node per triple, complement only on `lo`) stated in Lean as the
   representation invariant and the Go structure tested against it by
   randomized construction, in the style of `Oak.Modules` and
   `modules/`'s law tests.

3. **Hash-consed terms and id-keyed memos.** Build every term through
   one interning table so structural equality is pointer equality, key
   the blast memo on the `int32` id (a slice, not a map), and drop the
   per-evaluation maps in the witness pass for a slot frame indexed by
   variable id. Measurement: the blast benchmark. Proof: none new — the
   term algebra is unchanged; an intern table is a function.

4. **Better circuits.** Carry-lookahead or Kogge–Stone adders, a
   Wallace or Dadda multiplier for the widths in use, logarithmic popcount
   and count-leading-zeros (the `simd.popcount`/`ctz` shapes the codec
   track already relies on). Measurement: node counts for the arithmetic
   theorems. Proof: each circuit checked against the arithmetic
   definition by `bv_decide` in Lean for 8, 16, 32 and 64 bits, as
   `Oak.JsonDigits` checks the digit arithmetic today.

5. **Enumeration without the interpreter's heap.** Domains as packed
   `uint64` words, tuples as slot frames, the theorem body compiled once
   to a closure tree over slots (the ml lesson of working over the
   enabled set with static handles). Measurement: the effects and
   patterns files, which are enumeration-bound. Proof: a differential
   test against the interpreter over every theorem in `spec/oak`.

6. **Parallel theorems.** The ladder is embarrassingly parallel across
   theorems: a worker per core with a shared, read-only program and
   per-worker BDD engines. Measurement: wall on all three files. Proof:
   none — results are combined in declaration order.

7. **State exploration by fingerprint and bitset.** Liveness states as
   fixed-width packed words (the os model.oak lesson), visited sets as
   open-addressed fingerprint tables, edges in CSR arrays, Tarjan over
   arrays; symmetry reduction where the model declares interchangeable
   identities (what only two of os's 33 TLA+ specs used, and what made
   the difference there). Measurement: states per second on the largest
   pilot. Proof: the fingerprint table is sound only with a collision
   check on the packed state, stated and tested.

8. **One Lean extraction per run** in `prove_cmd.go` (N+1 compilations
   to 1), and a persistent `lake env lean` server for `:lean check`.
   Measurement: wall of `oak prove` on the lattice file with `-lean`.
   Proof: none.

9. **The test runner**: `NumCPU` workers by default, persistent worker
   processes fed cases over a pipe, results as a binary record instead
   of a temporary text file per case. Measurement: cases per second on
   the trivial-case benchmark. Proof: none; the replay fingerprint is
   unchanged.

10. **SAT, if and when a theorem needs it**: an in-repo CDCL with watched
    literals and LRAT output, checked by the existing LRAT checker, only
    after the BDD engine above stops being the bottleneck. Not before —
    the measured cost today is in tables and allocation, not in the
    decision procedure.

## 4a. First increment landed: the interpreter's scopes (item 5, first step)

The allocation profile of `BenchmarkTheoremsProtocols` (33 GB allocated in
19 s) put the cost in the interpreter's scopes, not in the deciders:
`object.NewEnclosedEnvironment` copied every declared ADT type into a
fresh map for every block, call and match arm; every scope allocated a
map for its bindings; `getBuiltin` rebuilt the table of builtin closures
on every identifier that was not in scope; a per-call map literal in the
primitive constructor; and each arithmetic operation asked the checker
for its width through a `fmt.Sprintf` key. The structures now: a scope is
one allocation holding four inline bindings and spills to a map only
past them (`object.Environment`, `inlineBindings`); ADT types are looked
up through the chain and never copied; blocks that declare nothing and
match arms that bind nothing evaluate in the enclosing scope; the builtin
table is built once; the checker's per-token tables are keyed by a struct
(`typechecker.tokenKey`) instead of a formatted string — a change the
checker itself pays for on every program. Semantics are unchanged: the
evaluator, checker, prover, REPL, backend and serializer suites pass
without modification.

| Benchmark | Before | After |
| --- | ---: | ---: |
| `BenchmarkTheoremsProtocols` | 19.98 s | 5.65 s |
| `BenchmarkTheoremsEffects` | 2.54 s | 1.04 s |
| `BenchmarkTheoremsPatterns` | 0.84 s | 0.22 s |
| `BenchmarkTheoremsLattice` | 3.78 s | 3.59 s (BDD-bound; item 2) |

What remains of item 5 is the structural step — slot frames resolved
once per function instead of name lookup per identifier, and the theorem
body compiled to a closure tree — which the remaining profile (match-arm
scopes at two thirds of the allocation, `Environment.Get` walking the
chain per identifier) now points at directly.

## 4b. Second increment landed: resident test-runner workers (item 9)

The runner's 62 cases a second were not the cases: a trivial property case
is microseconds of work, and the campaign's time was one process start per
case with the sanitizer runtime's initialization in each (measured on this
Mac at roughly 35 ms more per exec for a sanitized binary than a plain
one). The harness now has a resident mode (`test serve`): the runner
starts one harness process per concurrent case slot, sends each case as a
length-checked record on the worker's stdin, and the worker runs it in a
fresh `fork()` of itself — the child sees exactly the state a new process
would, so isolation and determinism are unchanged and every existing
report, timeout, shrink and replay path is untouched — then replies with
the wait status and the child's bounded output. A timed-out case kills the
worker's process group; the pool replaces workers on demand. Windows and
cross-built harnesses keep one process per case, as does `-resident=false`.

| Measurement | Before | After |
| --- | ---: | ---: |
| 500 trivial cases, `oak test -runs 500` | 7.84 s | 0.67 s |
| 2,000 trivial cases | 32.1 s (62 cases/s) | 1.83 s (1,090 cases/s) |
| `go test ./testrunner` | 74 s | 35 s |

## 4c. Third increment landed: the BDD engine's tables (item 2, first step)

The unique table and the operation cache are open-addressed hash tables of
fixed-width `int32` entries (linear probing, load factor at most one half,
growth by rehash) instead of Go maps keyed by structs. Node ids, insertion
order and every result are unchanged — the lattice file's largest diagram
is still 1,482,423 nodes and every proof and counterexample the same —
so the change is judged on throughput alone. Complement edges and a native
`ite` remain the second step of item 2; they change node identities and
so need the canonicity invariant stated first.

| Benchmark | Before | After |
| --- | ---: | ---: |
| `BenchmarkBDDMul12` (1,133,955 nodes) | 372 ms, 3.0 M nodes/s | 200 ms, 5.7 M nodes/s |
| `BenchmarkBDDAdd64` | 2.57 ms | 1.78 ms |
| `BenchmarkTheoremsLattice` | 3.59 s | 3.26 s |
| `BenchmarkTheoremsEffects` | 1.04 s | 0.83 s |

## 4d. Fourth increment landed: id-indexed witness evaluation (item 3, first step)

After the tables, the lattice profile's largest cost was not the diagrams
but the witness pass before them: every witness input evaluated the
theorem's term DAG through a fresh `map[*term]uint64` (3.5 GB allocated,
a fifth of the time). A `termEvaluator` numbers the subterms of the claim
and its traps once per theorem and remembers values in slices indexed by
that number under a generation stamp, so an input costs no allocation and
no hashing. The single-evaluation `eval` keeps its map through the same
`termMemo` interface, so the semantics (`Oak.AssemblerSemantics`) is one
body of code as before.

| Benchmark | Baseline | After tables | After the evaluator |
| --- | ---: | ---: | ---: |
| `BenchmarkTheoremsLattice` | 3.78 s | 3.26 s | 1.08 s |
| `BenchmarkTheoremsEffects` | 2.54 s | 0.83 s | 0.82 s |

Hash-consing the terms themselves (structural equality as pointer
equality, the blast memo keyed by id) is the rest of item 3.

## 5. What carries over from the codec track, unchanged

The discipline is the same one that took the derived JSON decoder from
1.20× to 0.81× of simdjson's time and the event workload from 1.72× to
0.91×: profile the actual hot loop before choosing a structure (lldb
program-counter sampling when Instruments is missing), pair every
measurement with a control in the same run, keep the slow path as the
authority so the fast structure can only accelerate and never decide,
and state the fact the fast structure relies on in Lean before landing
it. Items 2, 3, 5 and 7 are the same move as the array structural index
(§21): replace a pointer-chasing, allocating, map-keyed step by a flat,
indexed one whose correctness is a stated invariant.
