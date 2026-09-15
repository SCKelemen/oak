# The Tamarin projection of a protocol declaration (2026-09-15)

Specified in `docs/spec/112-protocols.md` §4b; not implemented. This
note holds the worked example in full and the reading rule an export
must state.

## Why a third reading

`oak prove` decides a protocol's invariants over the code's reading (the
first line whose guard holds, fixed-width arithmetic exact); TLC checks
the model-checker module over the every-line reading (§4). Tamarin's
multiset rewriting is also an every-line reading, with an unbounded
natural-number theory instead of widths. Three readings compared
pairwise is the correctness checklist's rule (`correctness.md` §2); the
projection is the third. It buys no security result — the declaration
has no message terms, no fresh names, no adversary — and says so in its
header.

## The Quantum declaration, projected

```oak
Quantum: protocol = {
  data { budget: u32, pending: Bool }
  init { budget: u32(2), pending: false }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
  park: Running -> Parked when !data.pending
  signal(on: Bool): Parked -> Parked then { data.pending = on }
  signal(on: Bool): Running -> Running then { data.pending = on }
  wake: Parked -> Running when data.pending then { data.pending = false }
}
```

```text
theory Quantum
begin
builtins: natural-numbers
/*
  oak protocol -tamarin Quantum.spthy spec/oak/machines.oak
  Reading: budget: u32 as a natural (%1 is one; %+ is addition); the
  naturals reading admits every trace of the width reading and more.
  Lines not projected: 0. Theorems not projected: 0. Entries out of scope:
  none (no fair or eventually entries in this declaration).
*/

// The state fact: St(control, budget, pending). Bool is 'true' | 'false'.

rule Init:
    [ ]
  --[ Init(), State('Running', %1 %+ %1, 'false') ]->
    [ St('Running', %1 %+ %1, 'false') ]

// tick: Running -> Running when budget > 1 then budget = budget - 1.
// Subtraction under the guard: budget is d %+ %1 with d >= 1, so the
// guard budget > 1 is d >= 1, written d = e %+ %1.
rule tick_Running_Running:
    [ St('Running', e %+ %1 %+ %1, pending) ]
  --[ Step_tick(), State('Running', e %+ %1, pending) ]->
    [ St('Running', e %+ %1, pending) ]

// tick: Running -> Yielded when budget <= 1 then budget = 2.
rule tick_Running_Yielded_0:
    [ St('Running', %1, pending) ]
  --[ Step_tick(), State('Yielded', %1 %+ %1, pending) ]->
    [ St('Yielded', %1 %+ %1, pending) ]
// budget = 0 has no natural spelling below %1 in this builtin; the
// exporter emits the case the init value and the effects can reach and
// names the omission in the header when it cannot.

rule resume:
    [ St('Yielded', budget, pending) ]
  --[ Step_resume(), State('Running', budget, pending) ]->
    [ St('Running', budget, pending) ]

rule park:
    [ St('Running', budget, 'false') ]
  --[ Step_park(), State('Parked', budget, 'false') ]->
    [ St('Parked', budget, 'false') ]

rule signal_Parked:
    [ St('Parked', budget, pending), In(on) ]
  --[ Step_signal(on), Bool(on), State('Parked', budget, on) ]->
    [ St('Parked', budget, on) ]

rule signal_Running:
    [ St('Running', budget, pending), In(on) ]
  --[ Step_signal(on), Bool(on), State('Running', budget, on) ]->
    [ St('Running', budget, on) ]

rule wake:
    [ St('Parked', budget, 'true') ]
  --[ Step_wake(), State('Running', budget, 'false') ]->
    [ St('Running', budget, 'false') ]

restriction Init_once:
    "All #i #j. Init() @ i & Init() @ j ==> #i = #j"
restriction Bool_payload:
    "All x #i. Bool(x) @ i ==> x = 'true' | x = 'false'"

// Sanity: every control state is reachable.
lemma reach_Running: exists-trace "Ex b p #i. State('Running', b, p) @ i"
lemma reach_Yielded: exists-trace "Ex b p #i. State('Yielded', b, p) @ i"
lemma reach_Parked:  exists-trace "Ex b p #i. State('Parked', b, p) @ i"

// The invariant theorem of the file, as an all-traces lemma:
//   budget_bounded: theorem (s: QuantumState, d: QuantumData) { d.budget <= u32(2) }
lemma budget_bounded: all-traces
    "All s b p #i. State(s, b, p) @ i ==> (b = %1 | b = %1 %+ %1)"
end
```

Two choices show where the projection bends: a guard that is a pattern
on the fact's argument (`e %+ %1 %+ %1` for `budget > 1`) rather than a
`Guard` action, which keeps the rule within the builtin's fragment; and
`budget = 0`, which the `natural-numbers` builtin does not spell, so the
`Yielded` line is emitted for the value the machine reaches and the
omission is counted in the header. A full exporter emits the `Guard`
action form of §4b when the pattern form is not available and lets the
restriction carry the guard.

## The reading rule

The naturals reading admits every trace of the width reading: a `u32`
field that would wrap at 2^32 keeps counting. So an `all-traces` lemma
verified in the projection holds for the code's reading only for traces
that never reach a width; `oak prove` decides the width reading exactly
(`paid__step` refutes at `coins: 255`, which no natural-number lemma sees).
A `falsified` lemma is a trace over the naturals to be replayed against
`oak prove` before it counts. The export's header states the direction;
`-check` prints it above the rows.

## What it would take to implement

- `protocol` command: `-tamarin path` beside `-tla`; the projection
  written from the same declaration reading the model-checker module
  uses (`prove/protocols.go` reads the declaration; the TLA+ writer is
  the shape to follow).
- The guard subset of §4, rewritten over fact arguments; subtraction as
  the `%+` pattern; `[N]Bool` unrolled; anything else counted and
  commented.
- `-check`: `exec` of `tamarin-prover --prove`, the summary block parsed
  by lemma name, rows in the prove shape; skipped by name without the
  binary.
- Tests: the Quantum text above as the golden projection; the check
  gated on the binary as the Lean check is.
- The security reading is a language decision (§7): message terms, fresh
  names, channels, an adversary in the declaration itself.
