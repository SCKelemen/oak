# Protocols: one declaration for the machine, every view derived

Status: implemented subset (this document is normative for it). The protocol
axis of the constitution — *how state may legally evolve* — gets a source
form whose single declaration drives the executable scaffolding, the typed
test commands of `110-testing.md`, and the model-checker module, over a
control graph with a declared data record, guards and effects. Typestate
APIs over resources are bound through the same declaration (§5).

## 1. Declaration

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

A finite control graph alone:

```oak
VirtualIrq: protocol = {
  initial Idle
  inject: Idle -> Pending
  acknowledge: Pending -> Active
  eoi: Active -> Idle
  program(compare: u16): Idle -> Idle
  program(compare: u16): Pending -> Pending
}
```

`protocol` is contextual, like `tag`: only `Name: protocol = {` reads as a
declaration, and `protocol` stays a legal identifier elsewhere. The body is a
sequence of entries separated by newlines or commas:

- `initial S` — exactly once. The initial control state.
- `data { field: T, ... }` and `init { field: value, ... }` — together or not
  at all: the machine's data record (an ordinary record type body) and its
  initial value (a record literal setting every field).
- `resource T` — zero or more nominal types the protocol governs (§5).
- `name(param: T)?: From -> To (when guard)? (then { effects })? (via callable)?`
  — one transition line. The guard is a Bool expression over `data.field`
  reads and the payload; the effects are statements over `data.field`
  assignments and the payload. Both use ordinary Oak and are checked by
  every gate once projected.

States are the names `initial` and the transition lines mention, in order of
first appearance with the initial state first; they are spelled like variants
(initial capital), because they become variants. Transition names are spelled
like functions; several lines may share a name (one step from several
states), and all lines of one name carry the same payload or none. A payload
is one fixed-width scalar or `Bool` — the shape typed test commands carry —
named so the model-checker module can quantify over it. Several lines may
share both name and source state when every such line carries a guard: in
Oak the first line whose guard holds is taken, in declaration order; the
model checker explores every line whose guard holds.

Shape errors (`OAK-M0301`): no `initial`, no transitions, a lowercase state,
a payload that is not a scalar, a payload that changes between lines of one
step, a `(name, from)` pair declared twice without guards, `data` without
`init` or `init` without `data`, an `init` that misses or invents a field, a
guard or effect that names `data` when none is declared, a `via` without a
`resource`, an initial state no transition leaves, and a projection whose
name the program already declares.

## 2. Projection into Oak

The declaration is replaced, before type checking, by ordinary declarations
built as typed syntax (compiler/synth.go, the derive mechanism) and checked
by every gate. For `Name` with `name` its snake_case:

| Projection | Shape |
| --- | --- |
| `NameState` | `type = S0 \| S1 \| ...` in state order |
| `NameStep` | `type = T0 \| T1(payload) \| ...`, one variant per step name (initial capital), payload as declared |
| `name_initial` | `(): NameState`, the initial state |
| `name_legal` | `(state: NameState, step: NameStep): Bool`, true exactly on declared `(from, step)` pairs |
| `name_next` | `(state: NameState, step: NameStep): NameState`; asserts legality (a located trap), then the declared target |

With `data`, the record joins the signatures:

| Projection | Shape |
| --- | --- |
| `NameData` | the declared record type |
| `name_initial_data` | `(): NameData`, the `init` value |
| `name_legal` | `(state: NameState, data: NameData, step: NameStep): Bool`: some line of the step leaves `state` and its guard holds on `data` |
| `name_next` | `(state: NameState, data: [*]NameData, step: NameStep): NameState`: asserts legality on `data[0]`, applies the first matching line's effects to `data[0]`, returns its target |

`pub` on the declaration exports every projection. The projections are the
executable state-machine scaffolding: a scenario keeps a `NameState` (and a
one-element `NameData` array it spans), asks `name_legal` before acting, and
moves with `name_next`; an illegal step is a bug in the caller and traps like
any failed assertion.

## 3. Deterministic-simulation actions

`NameStep` satisfies the typed-command shape of `110-testing.md`, so
`derive.test_generate`, `derive.test_encode` and `derive.test_decode` apply
to it unchanged. A generated history is then a sequence of protocol steps,
`name_legal` is the generator's legality predicate, and `name_next` is the
model. `examples/testing/protocol_test.oak` drives the machine above through
generated histories against a hand-written oracle of the same table.

## 4. Model-checker module

```text
oak protocol -tla Name [-o out.tla] file.oak
```

renders a TLA+ module from the parsed declaration alone: one `VARIABLE` per
data field plus `state`, `vars`, `States`, `Init` from `initial` and `init`,
one action per step name — the disjunction of its lines, each
`state = "From" /\ guard /\ state' = "To" /\ field' = value ... /\ UNCHANGED
<<rest>>`, with a parameter for the payload — `Next` as the disjunction of
the actions with payloads quantified over a declared `CONSTANT` per payload
name (`on` -> `On`), `TypeOK` (`Nat`, `Int`, `BOOLEAN` by field type), and
`Spec`. Guards and effects translate from the subset a line may use: field
reads, the payload, literals, width conversions, `+ - * / %`, comparisons,
`&& || !`, and `data.field = expr`; anything else stops the export naming
the line. The module is complete for what the declaration says and
checkable as is (TLC checks the modules of both examples above); scenarios
extend it for liveness and environment assumptions in a module of their own,
so regenerating never overwrites hand-written properties. The generated
header names the source it came from.

## 5. Resource protocols (`via`)

A transition line ending in `via f` binds the transition to the function `f`
that performs it. With at least one `resource T`, the declaration projects a
resource protocol fact (typechecker/resource_resolution.go): the protocol's
states, initial state, and one transition per `via` line, checked against the
typed program by the existing resource resolution. Lines without `via` stay
executable-only. Parameter modes are not declared in source yet and stay
unspecified; declaring them is part of §7.

## 6. What is not derived

Liveness and environment assumptions (fairness, device progress) are the
TLA+ extension module's; the declaration states what may happen, not what
must. Guards and effects beyond the translated subset — loops, calls into
the program, array data — stay in hand-written models. The declaration does
not generate Lean definitions, state diagrams, or debugger decoding
(constitution: the same fact should eventually drive them).

## 7. Direction

- Array-valued data (per-vCPU or per-slot state) with bounded indexing in
  guards and effects, the shape the OS's two-vCPU and interrupt-routing
  models need.
- Parameter modes on `via` lines (`borrowed`, `borrowed mut`, `consumed`) and
  typestate-indexed handle types.
- Conformance checking of a hand-written TLA+ module against the projected
  machine, for modules that predate the declaration.
