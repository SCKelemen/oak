# Note: a correctness-checklist pass over the protocol chapter

**Status: findings fixed the same day, one left open.** 2026-09-13,
`specification` branch. Target: `docs/spec/112-protocols.md` and the five
readings of one declaration — the projection into Oak
(`compiler/protocols.go`), the static projection
(`compiler/protocol_static.go`), the model-checker module
(`compiler/protocol_tla.go`), the prover's exclusivity theorems
(`compiler/protocol_exclusivity.go`), and the conformance monitor — after
the session's increments (mixed-symbol lowering, the monitor, record and
refined payloads, per-replica logs). Lists walked:
`docs/checklists/correctness.md` §2, §3, §5, §9, §11. The method is
`docs/checklists/README.md`. The question specific to this target: **do the
five readings of one declaration still agree?** Six findings were executed
(scratch programs through the interpreter and the module renderer), four by
reading.

## What the pass found

Severity: **break** (a stated behavior does not hold), **divergence** (two
readings differ and the chapter does not say so), **unstated** (a rule the
code enforces or relies on that the chapter does not state), **discipline**.

| # | Finding | Severity | Disposition |
| --- | --- | --- | --- |
| F1 | The projections bound their own locals under plain names — `done`, `result`, `record`, `from_i_k`, `d` — so a payload named `done` in a guard (`finish(done: Bool): Running -> Stopped when done`) read the generated flag: `name_next` never left `Running`, while the model-checker module read the payload. Executed. | break | **Fixed**: generated locals carry the `oak_` prefix; payload names `state`, `step`, `data`, `handle`, `m` and any `oak_*` are shape errors (§1, §2). |
| F2 | Projected names were compared with the program's declarations only, not with each other: a state `State` (`PState` twice), a step `monitor` (`p_monitor` twice), a protocol `FooBar` beside a state `Bar` of `Foo` (`FooBarState`) reached the type checker as a redeclaration of code the program never wrote. Executed. | break | **Fixed**: every projected name of every protocol is collected before any is appended; a duplicate is `OAK-M0301` naming both protocols (§1). |
| F3 | `TypeOK` said `Nat` for `u8`, `u16` and `u32` fields while the projection stores fixed widths; a module that let a field grow past 255 was type-correct to TLC. | divergence | **Fixed**: `TypeOK` uses the field's range (`0..255`, `0..65535`, `0..4294967295`, the signed ranges); `Nat`/`Int` remain for 64-bit fields (§4). |
| F4 | An index by the payload without a written bound (`put(cmd: Cmd): Open -> Open then { data.cells[u32(cmd.slot)] = cmd.value }`) was a trap in `name_next`, a violation-free `true` in `name_legal`, an evaluation error in TLC, and a trap in the static projection. Executed. | divergence | **Fixed**: every index into an `[N]T` path adds `i < u32(N)` to the line's effective guard, inner indexes first, and all five readings take the guard from one place (`lineGuard`); the step is illegal everywhere and `Refused` statically (§1, §2b). A constant index out of range is a shape error. |
| F5 | A `when` guard on a `via` line was accepted; the resource checker never reads guards, so the dynamic projection alone enforced it. Executed. | unstated | **Fixed**: refused (§1, §5). |
| F6 | §2b's table left the handle parameter's spelling and the outcome variants' spellings unstated against the payload names a user may choose. | unstated | **Stated** (§2b). |
| F7 | The TLC configuration's default payload domain was `{0, 1, 2, 3}` regardless of the literals the guards compare against: a guard `n < u8(5)` was explored only below its boundary. Executed. | divergence | **Fixed**: the domain runs from 0 through one past the largest literal in the guards and effects, at least `0..3`, clipped to the type (§4). |
| F8 | "A state no transition reaches" was decided on *mentioned* states: `b: Z -> X` made `Z` a state no path from `initial` reaches, explored by no reading, proved about vacuously. Executed. | break | **Fixed**: reachability is a walk from `initial`; an unreached state is a shape error, and `eventually` is checked against the reached set (§1). |
| F9 | The monitor's `violations` counter wrapped at 2^32 back to conforming. | unstated | **Fixed**: saturates (§2c). |
| F10 | Eleven functions of the projection code exceed seventy lines (`project` alone near 300). | discipline | **Open**: split by reading (state-less, data-carrying, lowering) when the next increment touches `project`. |

One finding the fixes made: the first cut of F4 ordered a nested bound
(`replicas[who].len < 3`) before the bound protecting the index inside it
(`who < 2`) when the declared guard already spelled the latter and the
bound was deduplicated against it — the prover's reachable-state
enumeration trapped (`prove/replica_logs_test.go`). Bounds are now emitted
in post-order and never dropped in favor of the guard, which is why a
module may spell one bound twice.

## Disposition summary

Of the checklist items with a bearing: **yes** for §2 small model then big
test, refinement mappings (§4a), counterexamples (the exclusivity rows),
§3 typestate for the machine itself (§2b), §11 deterministic output and
reconciliation of the chapter with the code (this pass); **no, now fixed**
for §2 the model's domain (F3, F7), §5 hygiene of generated code (F1),
§11 collisions found before the checker (F2), §9 totality on the
generator's domain (F4), §11 the error list indexing the sections (F5,
F8); **no, open** for §5 function length (F10).

## Verified claims

Checked against code and, where marked, by execution: the first-line
reading (`name_next`) and the every-line reading (TLC) coincide exactly
when the exclusivity theorems hold, and the theorems now range over the
effective guards; the static projection's `Refused` is exactly
`name_legal` false, index bounds included (executed:
`compiler/e2e_protocol_pass_test.go`); the lowering (§2a) is untouched by
the pass, since a machine without data has no indexes; the spec's four
example programs (`examples/testing/protocol_test.oak`,
`protocol_data_test.oak`, `examples/verification_quantum.oak`,
`benchmarks/state-machines/utf8_protocol.oak`) and `spec/oak/protocols.oak`
pass the new shape rules unchanged; the record-payload and slots modules
still self-conform under the added bound. No Lean statement joins this
pass: the fixes are to the generators, and the shared meaning
(`Oak.Protocol`, `Oak.ProtocolQuorum`, `Oak.Typestate`) is unchanged.

## What the target taught the lists

Written back into `docs/checklists/correctness.md`: every reading of one
declaration is compared pairwise on domain, width, partiality, and choice
(§2, new); a conjunct one reading needs binds every reading, ordered so it
never needs the guard it protects (§2, new); the model's default domain
covers the literals (§2, new); reach is computed, not assumed (§2, new);
generated code is hygienic (§11, new); collisions are found before the
checker (§11, new); the error list indexes the sections (§11, new).

## Revisit criteria

- F10: the next increment that edits `project()` splits it by reading
  first.
- The two-fold bound in module text: when a module is compared by text
  against a hand-written one (§4a), the comparison is semantic, so the
  repetition costs nothing; if a golden-text workflow appears, fold a bound
  the guard's *first* conjunct already spells.
- Reserved payload names are a list; if the projections gain a parameter,
  add it to `reservedPayloadName` and §1 in the same change.
