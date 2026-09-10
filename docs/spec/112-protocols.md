# Protocols: one declaration for the machine, every view derived

Status: implemented subset (this document is normative for it). The protocol
axis of the constitution — *how state may legally evolve* — gets a source
form whose single declaration drives the executable scaffolding, the typed
test commands of `110-testing.md`, and the model-checker module. Typestate
APIs over resources are bound through the same declaration (§5); guards and
data over the control graph are direction (§7).

## 1. Declaration

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
- `resource T` — zero or more nominal types the protocol governs (§5).
- `name(param: T)?: From -> To (via callable)?` — one transition line.

States are the names `initial` and the transition lines mention, in order of
first appearance with the initial state first; they are spelled like variants
(initial capital), because they become variants. Transition names are spelled
like functions; several lines may share a name (one step from several
states), and all lines of one name carry the same payload or none. A payload
is one fixed-width scalar or `Bool` — the shape typed test commands carry —
named so the model-checker module can quantify over it.

Shape errors (`OAK-M0301`): no `initial`, no transitions, a lowercase state,
a payload that is not a scalar, a payload that changes between lines of one
step, a `(name, from)` pair declared twice, a `via` without a `resource`, an
initial state no transition leaves, and a projection whose name the program
already declares.

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

`pub` on the declaration exports every projection. The projections are the
executable state-machine scaffolding: a scenario keeps a `NameState`, asks
`name_legal` before acting, and moves with `name_next`; an illegal step is a
bug in the caller and traps like any failed assertion.

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

renders a TLA+ module from the parsed declaration alone: `VARIABLE state`,
`States`, `Init`, one action per step name — the disjunction of its
`state = "From" /\ state' = "To"` lines, with a parameter for the payload —
`Next` as the disjunction of the actions with payloads quantified over a
declared `CONSTANT` per payload name (`compare` -> `Compare`), `TypeOK`, and
`Spec`. The module is complete for the control graph and checkable as is;
scenarios that need data, guards or liveness extend it in a module of their
own, so regenerating the control graph never overwrites hand-written
properties. The generated header names the source it came from.

## 5. Resource protocols (`via`)

A transition line ending in `via f` binds the transition to the function `f`
that performs it. With at least one `resource T`, the declaration projects a
resource protocol fact (typechecker/resource_resolution.go): the protocol's
states, initial state, and one transition per `via` line, checked against the
typed program by the existing resource resolution. Lines without `via` stay
executable-only. Parameter modes are not declared in source yet and stay
unspecified; declaring them is part of §7.

## 6. What is not derived

Guards over data, effects on data, and liveness are the scenario's and the
TLA+ extension module's; the protocol declares the control graph only. The
declaration does not generate Lean definitions, state diagrams, or debugger
decoding (constitution: the same fact should eventually drive them).

## 7. Direction

- Guards and effects over a declared data record, so the legality predicate
  and the transition function carry data and the TLA+ actions carry the
  same guards — the point at which the OS's scheduler, wakeup, wiring and
  call-gate models stop being written three times.
- Parameter modes on `via` lines (`borrowed`, `borrowed mut`, `consumed`) and
  typestate-indexed handle types.
- Conformance checking of a hand-written TLA+ module against the projected
  control graph, for modules that predate the declaration.
