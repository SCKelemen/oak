# Native testing, generated inputs, fuzzing, and simulation

Status: initial executable host tooling and Oak helper library. `tested` is not
`proved`, `model-checked`, or a refinement witness. This document specifies the
implemented bootstrap contract and explicitly identifies its limits.

## Entry points and discovery

`oak test [flags] [directory | ./... ...]` compiles each selected directory as
one bootstrap package through the ordinary checked C backend. Flags precede
paths. An omitted path means the current directory. Recursive discovery skips
hidden directories, `vendor`, and `testdata`. Discovery and execution order are
stable, and overlapping directory arguments are deduplicated.

All immediate `.oak` siblings participate in the compilation. Only top-level
functions in `*_test.oak` register tests. Names have an ASCII identifier spelling
and start with a prefix followed by an uppercase ASCII letter or underscore:

| Prefix | Signature | Ordinary `oak test` behavior |
| --- | --- | --- |
| `Test` | `(): ()` | One execution |
| `Property` | `(data: []u8): ()` | Corpus plus generated cases |
| `Fuzz` | `(data: []u8): ()` | Corpus plus four built-in seeds |
| `Sim` | `(data: []u8): ()` | Corpus plus generated simulation inputs |
| `Table` | `(row: []u8): ()` | One execution per row file under `testdata/oak/<Test>/rows` |

Methods, generic tests, extern tests, variadics, and other signatures reject.
All functions still undergo the normal type, borrow, and discipline checks.
The application `main` is compiled but is not used as the test entry point.
`-run` filters all kinds; `-fuzz` selects mutation fuzz campaigns; `-sim` selects
simulation campaigns. No matching tests is an error, including empty discovery.
`-list` discovers and validates registrations without native compilation.

Bootstrap package source is concatenated in filename order with source-boundary
comments. Test registrations retain original filename and line. Compiler errors
currently refer to positions in the assembled `<oak-test-package>` source.

A directory whose `.oak` files all open with the same package clause is a
module package (`83-modules.md`). It compiles through the module loader with
the root package's `*_test.oak` files included, so tests may use `pub` members,
imported packages resolved through the enclosing `oak.mod`, and the simulation
profile. Mixing files with and without a clause in one directory rejects. The
root package's C symbols carry the package prefix (`oak_<package>_<Name>`)
unless it is `package main`; the harness uses the same renaming as
`compiler/modules.go`. Only the root package's test files join the build:
imported packages are compiled as their clients see them.

## Isolation, outcomes, and reporting

Every normal runner case starts a fresh native child process. Assertions and
bounds traps cannot terminate the host runner. `-timeout` bounds each execution;
`-build-timeout` bounds C compilation. Native stdout/stderr and the control
report are independently bounded to 64 KiB. Excess user output is truncated;
control-report overflow fails the case. The control report is separate from
stdout, so ordinary test output cannot corrupt `-json` results.

This is process isolation for trusted development tests, not a security sandbox.
Tests may use the host permissions available to them. Sanitizers are opt-in via
`-sanitize` and require a supporting C compiler/runtime.

`import(testing)` provides:

- `test_check(condition, id)`: fail with an author-assigned stable `u32` invariant
  ID. The explicit C reporting boundary is supplied by the host harness.
- `test_assume(condition)`: reject an input. Rejections do not count as passing
  cases; exceeding `-max-discards` fails. A unit test cannot discard.
- `testing_classify(id)`: mark a class reached in this execution. Each accepted
  execution counts once per class, even if a loop emits it repeatedly.
- `testing_trace(id, a, b)`: record an author-defined semantic event with a
  stable `u32` ID and two `u64` payloads. Values are observations, not choices:
  the call consumes no choice-tape bytes and does not affect scheduling.
- `-cover 10:5,20:1`: require minimum accepted-case counts for these class IDs in
  each selected non-unit test. These are semantic labels, not code coverage.

Ordinary `assert` remains always enabled. A generic trap has an exit/signal
signature; `test_check` provides stronger failure identity for minimization.
Source-specific assertion diffs, subtests, cleanup callbacks, expected-trap
annotations, and compile-fail registration are not yet part of this API.

## Choice tapes and property testing

A `TestChoices` cursor consumes a caller-supplied byte view through `test_byte`,
`test_bool`, `test_u32`, and `test_range`. Unsigned words consume four bytes in
little-endian order. Exhaustion supplies zero without advancing the cursor.
Thus every finite tape describes a complete run. There is no hidden target
allocation. Separate the host's storage needs from the effects of tested code.

Generators are ordinary composable Oak functions over the cursor and tape.
Dependent generators construct valid values from previous choices. Stateful
tests construct legal command sequences and compare execution with a separately
represented model; see `examples/testing/irq_test.oak`. Do not repair arbitrary
raw-memory encodings into unsafe values or assume every proposition admits an
efficient generator. Automatic ADT/refinement derivation is future work.

`test_range` is inclusive and handles the entire `u32` domain without overflow.
Its modulo mapping is deliberately biased; no uniform or cryptographic sampling
claim is made. The runner includes empty, zero-filled, 0xff-filled and ascending
byte seeds, then variable-length generated tapes. Root seed, target name, and
attempt independently derive a fixed SplitMix64 stream. There is no dependence
on Go's random implementation or earlier tests consuming random numbers.

Failure minimization deletes chunks and then reduces bytes. Every accepted
candidate is smaller by length or lexicographic order and must reproduce the
same failure signature. Both an execution budget and a time budget apply. One
in-flight execution may extend the shrink deadline by at most its case timeout.
An initial repeat checks failure stability. Timeouts and harness failures are
saved but not minimized. The result is budget-minimized, not globally minimal.
Stability confirmation compares recorded traces too. A final execution confirms
the minimized input and supplies its trace and output; it must match the last
accepted reduction's trace. If it diverges, retain the original input/evidence
and report instability. Initial/final confirmation executions are additional to
the reduction budget and each uses the ordinary per-case watchdog.
A generic signal signature cannot distinguish two unrelated traps with the same
signal; stable invariant IDs are preferred for stateful properties.

## Campaigns

Every generated attempt is a pure function of the root seed, the test name and
the attempt index, so a campaign is the prefix of one deterministic sequence.
`-workers N` (1..64) prepares and executes up to `N` attempts concurrently and
then consumes their outcomes in attempt order: counts, discards, coverage, the
failing attempt and its minimized input are identical for every worker count.
Attempts prepared beyond the stopping point are executed but never counted.
Each execution writes its own control report, so concurrent cases never share a
file. Minimization and corpus replay remain sequential.

`-campaign dir` makes a campaign resumable. After every batch the runner writes
`<dir>/<Test>-<package digest>.json` with the engine and build identity, seed,
input limit, sanitizer mode, next attempt, and the accepted, case, discard and
class counts. A later invocation with the same identity continues from the next
attempt with those counts, so `-runs 1000000` can be split across many jobs
over time; a satisfied campaign does no new work. State from a different build,
test, seed or configuration rejects rather than mixing sequences. Results report
`attempts`, the consumed prefix length including resumed attempts. Sharding
across machines needs no extra mechanism: give each shard a distinct `-seed`.
`-replay` never combines with a campaign.

## Corpus and replay

Failures are atomically saved in `testdata/oak/<TestName>/<digest>.json` with:

- schema and engine versions;
- test name and kind;
- native build fingerprint;
- root seed and attempt;
- maximum input size, execution timeout, and sanitizer mode;
- failure signature and concrete minimized input (JSON base64).
- optional trace schema version, recorded semantic events and truncation flag.

The build fingerprint covers generated C, the harness, native compilation flags,
C compiler version output, and any adapter manifest and object hashes. It is a useful drift check, not an attestation of
all host libraries, environment variables, CPU features, or external effects.
Exact replay still requires preserving the relevant execution environment.

`-replay artifact.json directory` executes exactly one concrete input and checks
both the build fingerprint and failure signature. A reproduced failure exits
nonzero. Divergence is reported explicitly, including a now-passing input.
Filtering does not change the compiled registration table, so selecting one test
for replay does not itself invalidate a multi-test failure artifact.

New artifacts carry trace version 1. The first 256 events are retained in order;
an additional event sets `trace_truncated` without changing the test outcome.
Each event has `id`, `a`, and `b`; the 64-bit payloads are JSON decimal strings
to avoid precision loss in JavaScript tooling. Events are flushed immediately,
preserving an available prefix after a trap or watchdog termination. Trace
storage shares the existing bounded control report. The terminal prints the
last eight retained events; the artifact and JSON result contain the entire
retained prefix. Successful/discarded cases do not expose traces in results.

Strict replay requires the same trace prefix and truncation flag, even when the
invariant ID matches. This detects observed divergence; it does not prove that
unrecorded behavior or a truncated suffix was identical. Legacy artifacts with
no trace version retain their original input/build/signature replay contract.
A diverging replay reports the index of the first recorded event the observed
trace did not reproduce, with both events; a trace that ends early reports the
missing side. JSON results carry it as `trace_divergence`.

## Table targets

A `Table` target is data-driven conformance: the inputs are not generated,
they are the files of `testdata/oak/<TestName>/rows/`, and each file is one
row. The runner executes the rows once each in file-name order, skipping
directories and dotfiles, and counts each executed row as a case. `-runs`,
seeds, and the failure corpus do not apply: the rows are the corpus. A target
whose rows directory is missing or empty is an error, never a vacuous pass;
a row larger than `-max-bytes` is an error rather than a truncated case.

The row's bytes reach the test as the `[]u8` argument. The row format is the
test's own; `import(testing)` provides little-endian readers `test_row_u32`,
`test_row_u64`, `test_row_f32`, and `test_row_f64` at a byte offset, which
trap on a short row, so a row of fixed-width fields is decoded by offset
without a codec. The ordinary `test_check`, `testing_classify`, and
`testing_trace` apply; `test_assume` discards the row.

Failure identity is the row: the result names the failing row (`row` in the
JSON result, `row <file>: <signature>` in the failure text), the saved
artifact carries the row name and the row bytes as its input, and the row is
never minimized (a shrunk row is no longer the row). `-replay` of such an
artifact executes the saved row. Execution stops at the first failing row so
the reported row is the first in name order; name rows so that the order is
the one the table's author wants read first.

Floating-point fields compare by ULP distance or by exact bits, never by
`==`: `test_ulp_distance_f32`/`test_ulp_distance_f64` count the representable
values between two numbers (`+0` and `-0` are one value, two NaNs are at
distance 0, a NaN against a number is the maximum distance),
`test_check_ulps_*(got, want, ulps, id)` fails the row unless the distance
is within `ulps`, and `test_check_bits_*(got, want, id)` demands identical
bit patterns — the check for a bit-exact contract such as the `math`
package's (`20-types.md` §11.3.6). A numeric conformance table produced by
another implementation is therefore a directory of rows and a `Table`
function of a few lines, and its report says which row disagreed.

## Trace schema

A package may describe its events in `oak-trace.json` next to its tests:

```json
{"version": 1, "events": {"401": {"name": "command",
  "a": [{"name": "kind", "shift": 32, "bits": 32, "names": {"0": "admit"}},
        {"name": "target", "shift": 16, "bits": 16}],
  "b": [{"name": "ticks"}]}}}
```

Each field selects `(payload >> shift) & mask(bits)`; omitting both takes the
whole payload, and `names` maps decimal values to labels. The schema decodes
terminal output, the `trace_text` array of JSON results, and divergence
reports. It never changes what is recorded, compared, or replayed: artifacts
keep raw events, unknown IDs print raw, and a package without a schema behaves
as before. A present schema must be valid (version 1, u32 event keys,
identifier names, fields inside 64 bits, at most 1 MiB), because decoded output
that silently fell back to raw values would mislead.

Ordinary test runs replay corpus inputs before generating new ones and do not
require the historical build fingerprint: checked-in regressions must survive
source changes. `.bin` files in the same directory are additional raw seeds.
Unknown/malformed artifact schemas, mismatched test identities, and oversized
inputs reject. Commit valuable minimized failures, not random campaign output.

## Fuzzing

`-fuzz` uses deterministic byte insertion, deletion, bit flips, replacement and
fresh-input exploration over corpus/built-in seeds. This portable engine is
mutation fuzzing, not coverage-guided fuzzing. `-runs` is a finite accepted-case
budget, making it usable in CI.

`-fuzz '^FuzzName$' -emit-fuzz-harness path.c` emits one checked translation unit
with `LLVMFuzzerTestOneInput`. Compile it with Clang's
`-fsanitize=fuzzer,address,undefined` for coverage-guided native fuzzing. Export
requires one target and refuses to overwrite an existing file. The emitted
harness preserves invariant IDs, skips oversized input, and translates rejected
inputs to a return to libFuzzer. libFuzzer owns its corpus, crash files and
minimization. Copy useful raw crash files into the runner's `.bin` corpus to
reproduce and reduce them with `oak test`.

Trace calls are no-ops in persistent libFuzzer exports. Replay a raw crash input
through the isolated runner to collect a bounded semantic history.

libFuzzer is persistent: all tested state must be constructed/reset inside the
fuzz function. Target-side state must not escape across calls. Avoid nontrivial
resource cleanup obligations around `test_assume` in this mode: rejection uses
a host `setjmp`/`longjmp` boundary. The ordinary isolated runner does not require
persistent-process reset discipline.

## Deterministic event simulation

`SimClock`, `SimQueue`, and caller-owned `SimEvent` storage implement a bounded
discrete-event queue. Scheduling in the past rejects; full capacity returns
false without altering the queue. `sim_next` advances to the earliest event and
uses a choice to select among equal-time events. Removing an event swaps in the
last slot; this deterministic storage order is part of this version's replay
contract. Queue operations are bounded linear scans. Empty dequeue rejects.

Scenario code owns production state, independent models, allowed fault actions,
and invariants. It also owns finite step budgets. The IRQ/timer pilot checks
state transitions and a recovery suffix with explicit progress assumptions.
The host additionally applies a watchdog to runaway test code.

Packages containing any registered `Sim` test compile with `WithSimulation`.
The compiler checks the complete imported syntax tree before specialization,
including unused functions, generic templates, closures and global initializers.
Unsafe blocks, `Atomic` storage/operations, machine library names, and undeclared
extern functions reject. C scalar conversions and portable SIMD remain available.
This deliberately conservative check also rejects shadowed machine names; it is
a whole-package boundary restriction, not a reachability-based effect proof.
The same profile applies when selecting another test or exporting fuzz code from
that package, preserving replay identities across filtering.

Only the actual imported testing reporter declarations are automatically
trusted. User declarations cannot obtain that trust by copying a reporter name
or symbol. Other foreign boundaries require an explicit native adapter.
No arbitrary clocks, entropy, MMIO, threads or atomics are automatically
intercepted. Integration with the OS's replay/debug event schema remains
future work; simulated storage, crashes and scheduling adapters are below.
Single-thread event interleavings are not an ARM weak-memory model and do not
replace the existing memory-model litmus tests or hardware validation.

## Simulated storage

`SimDisk` and the `sim_disk_*` functions are a deterministic block device for
simulation scenarios: pure Oak in the testing module, over caller-owned
storage, with no native adapter. A device has `blocks × words` `u64` words in
two copies — the volatile copy that reads see while the device is running and
the durable copy that survives a crash — and two provenance flag words per
block, one per copy. `sim_disk_init` sizes and zeroes it; `sim_disk_write`
writes one block from a caller span and marks it dirty; `sim_disk_fsync`
persists every dirty block; `sim_disk_read` copies one block into a caller
span and reports failure; `sim_disk_crash` drops every unpersisted write and
reverts each block to its durable copy and provenance; `sim_disk_restart`
brings the device back.

Faults are explicit actions drawn from the choice tape, never ambient. A
`faults` mask enables them per operation: torn write (a prefix of the block
persists), misdirected write (it lands in another block; the target keeps its
content), dropped write (acknowledged, never landed), lost fsync (acknowledged,
one dirty block stays undurable), bit flip on read (one bit, both copies), and
latent sector error (the read fails until the block is rewritten). One roll in
eight injects a fault, chosen among the enabled kinds that apply; the tape's
exhaustion value never injects one, so a shrunk tape is a run with fewer
faults and strict replay reproduces each one. Every fault increments its
counter on the device and marks the copies it touched: 2 torn, 4 misdirected,
8 stale (an acknowledged write never landed here), 16 corrupted, 32 latent,
with 1 for dirty. `sim_disk_trusted` and `sim_disk_durable_trusted` report a
block with no fault mark on the volatile or durable copy. A clean rewrite
heals the volatile copy; an fsync that acknowledges a stale block makes its
durable copy stale too.

The ledger is the scenario's contract. Durability obligations apply to trusted
blocks; detection obligations — checksums, sequence numbers, epochs — apply to
the rest. The bundled write-ahead-log scenario (`examples/testing`) states the
three a single-disk log can honestly keep: no phantom record unless its block
is untrusted, recovery is a prefix of what was appended, and every acknowledged
record on a trusted block is recovered up to the first untrusted acknowledged
block. Without faults the device is exact against a two-copy model.

## Crashes and scheduling

A crash is an event, not a call. `sim_process_schedule_crash` enqueues a
crash and its restart with tape-chosen delay and downtime, as two events of
kinds the scenario names; it schedules nothing when the queue lacks room for
both, so a crash never lands without its restart. The scenario's event loop
dispatches the crash kind to `sim_process_crash` (and, for a device,
`sim_disk_crash`) and the restart kind to `sim_process_restart` followed by
its own recovery code, so recovery runs inside the simulated timeline like
every other action. `SimProcess` records what the scenario must honor: no
operation while down, an epoch per restart (`restarts`), and when it went
down. Overlapping crash windows are the scenario's to collapse.

`sim_schedule_delayed` schedules an event a tape-chosen 0..max delay later
than asked; with `sim_next`'s tie choice this lets the tape reorder events
that were not simultaneous. `SimSched` is a fair scheduling adapter over up
to 32 actors with caller-owned wait counters: `sim_sched_pick` draws the next
actor from the tape among the runnable ones, except that once a runnable
actor has waited `bound` consecutive picks the longest waiter is picked
(ties to the lowest index). Several actors may reach the bound together and
are served one per pick, so a runnable actor waits at most `bound + actors -
2` picks — the fairness assumption liveness invariants rely on, exposed by
`sim_sched_max_wait`. A non-runnable actor is not waiting. The bundled
event-driven log scenario (`examples/testing`) schedules two writers through
the adapter and crashes through the process helper, keeping the storage
invariants above plus fairness.

## Trusted native adapters

`-adapter manifest.json` links a prebuilt native adapter. The version-1 manifest
requires a name, `deterministic: true`, exact Oak binding names/C symbols, scalar
ABI signatures, and 1..32 `.a`/`.o` objects with SHA-256 digests. Parameters and
results are fixed-width signed/unsigned `c.Int8` through `c.UInt64`; `()` is also
allowed as a result. Pointer/variadic interfaces are intentionally excluded.
`oak_` symbols are reserved for generated code and the testing harness.

```json
{
  "version": 1,
  "name": "my-device-v1",
  "deterministic": true,
  "bindings": [
    {"name": "device_step", "symbol": "device_step_native",
     "parameters": ["c.UInt32"], "return": "c.UInt32"}
  ],
  "objects": [{"path": "build/device.a", "sha256": "<64 lowercase hex digits>"}]
}
```

Object paths resolve relative to the manifest. The runner verifies and snapshots
their bytes before linking. Thin archives, shared libraries and linker scripts
reject; accepted inputs are self-contained archives or ELF relocatable objects,
at most 64 MiB each. Manifest/object identities enter the replay fingerprint;
locator paths do not. Supply `-adapter` again for replay and preserve the original
objects. Replay artifacts never cause automatic native-code loading.

The manifest is an explicit assertion of trust, **not proof of native code's
determinism**. Adapter code must route time/entropy/scheduling through explicit
inputs, reset state for each scenario, and avoid unmodeled host effects. Normal
type/borrow/discipline checks still apply to the Oak program. This is not a
security sandbox or runtime syscall filter.

Fuzz export validates the adapter and records its manifest identity in the C
file; link the pinned objects explicitly when compiling that export. The external
link command and any instrumentation of the adapter are the caller's responsibility.

## Validation

Go tests execute compiled Oak programs for registration, native unit/property/
fuzz/simulation modes, rejection budgets, coverage labels, crash and timeout
isolation, minimization, strict replay, source drift, and corpus reuse. A mutation
test deliberately drops edges arriving while active in the IRQ
pilot and requires the model to detect invariant 2011 with the four-command
counterexample `enable, inject, acknowledge, inject`. Go fuzz targets exercise
reducer invariants and mutation bounds. The dedicated workflow
runs the native Oak examples and a coverage-guided libFuzzer smoke campaign.

## Stateful command properties

A `GeneratePropertyName(data: []u8): ()` companion in a `*_test.oak` file
opts `PropertyName` into concrete command histories. `GenerateSimName` works the
same way for `SimName`. Companions are not separately registered tests. Unit and
fuzz targets cannot have companions in this version.

Use `TestChoices` to select legal operations against an independent model, then
emit each operation with `testing_command(TestCommand { kind: ..., target: ...,
value: ... })`. Emit at most `testing_command_limit()` commands, which is
`min(256, -max-bytes / 12)`. Exceeding the limit or emitting during execution is
a harness error. Generation runs in its own isolated process; target execution
starts in a fresh process. Generator discards consume the discard budget.

The target receives concrete commands, not the generator's random tape.
`test_command_count(data)` validates alignment; `test_command_at(data, index)`
decodes a command. Validate the **entire** history against model preconditions
with `test_assume` before exercising the implementation. Reject unknown kinds,
invalid identifiers and missing prerequisites. Then reset the model and compare
each real operation with its model transition. Domain structs/enums can be
mapped to this fixed three-word carrier; arbitrary type derivation is not yet
provided. Share one legality predicate between the generator and the target so
the generator never emits a history the target would reject.

Shrinking deletes whole commands and reduces unsigned target/value fields,
repeating both passes until a round makes no progress or the budget ends, so a
command made redundant by a smaller field is removed too. Kinds remain fixed. A candidate is retained only when execution reports the
same invariant. Model preconditions therefore preserve dependencies: deleting
a create operation must invalidate a later use of that object. The reducer does
not infer references or rewrite IDs. Its bounded greedy search does not promise
a globally minimal history.

Artifacts record `input_format: "commands-v1-u32x3le"` and the concrete input as
three little-endian u32 words per command. JSON results include decoded commands;
terminal failures print them. Corpus runs, shrinking and strict replay bypass
generation entirely. Raw `.bin` corpus entries must already have this encoding;
JSON corpus entries must match the input format. Trace replay retains the same
build and semantic-trace checks as byte properties. A generator failure is a
harness error, not a minimized target counterexample.

### Typed commands

A command sum type derives its generator, carrier encoding, and decoder
(`83-modules.md` section 6.6): each variant carries Unit, one carrier scalar
(`u8`, `u16`, `u32`, `Bool`), or a closed record of at most two carrier
scalars. The type's own package declares:

```oak
SleepArg: type = struct { task: u8, ticks: u8 }
Cmd: type = Admit: u8 | Sleep: SleepArg | Tick
cmd_generate: (choices: [*]TestChoices, data: []u8): Cmd = derive.test_generate
cmd_encode: (v: Cmd): TestCommand = derive.test_encode
cmd_decode: (command: TestCommand): Option[Cmd] = derive.test_decode
```

`test_generate` draws the variant with `test_range` and each scalar from its
full range; `test_encode` packs the variant index as `kind`, the first scalar
as `target`, the second as `value`, with unused words zero; `test_decode`
accepts exactly the encodings `test_encode` produces (range-checked, unused
words zero) and returns `None` otherwise. The encoding is injective and
canonical, so the command reducer moves through decodable commands toward the
smallest payloads, and a target that rejects `None` with `test_assume` never
executes an undecodable history. `Option` requires `import(std)`. Any other
payload shape rejects (`OAK-M0203`); a wrong signature rejects (`OAK-M0202`).
Model preconditions and legality remain the author's: derivation supplies the
plumbing, not the semantics.

`examples/testing/irq_test.oak` contains `PropertyIrqCommands`: acknowledgement
is legal only in a deliverable model state and EOI only in an active one. The
Go mutation test injects the lost-edge bug into a nine-command legal history and
requires the reducer to reach exactly `enable, inject, acknowledge, inject`;
every intermediate candidate that removed the enabling command was rejected by
the target's preconditions rather than accepted as a spurious shorter failure.
A Go fuzz target checks that command minimization preserves alignment, never
introduces a command kind, never grows, and never loses a reported failure.
