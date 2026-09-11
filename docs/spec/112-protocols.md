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
  at all: the machine's data record (an ordinary record type body; fields
  may be fixed arrays `[N]T`) and its initial value (a record literal setting
  every field; arrays as typed array literals).
- `resource T` — zero or more nominal types the protocol governs (§5).
- `name(param: T)?: From -> To (when guard)? (then { effects })? (via callable)?`
  — one transition line. The guard is a Bool expression over `data.field`
  and `data.field[i]` reads and the payload; the effects are statements over
  `data.field = e` and `data.field[i] = e` and the payload. Both use ordinary
  Oak and are checked by every gate once projected. An index is checked at
  run time like any Oak index, so a guard that indexes by the payload
  bounds it first (`u32(who) < u32(2) && data.parked[u32(who)]`); the
  model-checker module gets the same conjunct and a payload domain that
  matches.

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
guard or effect that names `data` when none is declared, a data field named `state`, `step` or `data` (the projection's own names), a `via` without a
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
| `name_next` | `(state: NameState, data: [*]NameData, step: NameStep): NameState`: asserts legality on `data[0]`, copies the record out, applies the first matching line's effects to the copy, writes it back through the span, returns its target |

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
and element reads, the payload, literals, width conversions, `+ - * / %`,
comparisons, `&& || !`, `data.field = expr`, and `data.field[i] = expr`
(element stores on one array fold into one `[field EXCEPT ![i] = v, ...]`);
an `[N]T` field is a function `[0..N-1 -> T]`, initialized as one arrow
when every element agrees and as a `CASE` otherwise; anything else stops the
export naming the line. The module is complete for what the declaration says and
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
executable-only.

The callable may carry its **resource parameter modes** in parentheses:

```oak
Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via inspect(borrowed h)
  shut: Open -> Closed via close(consumed h)
  join: Open -> Open via merge(borrowed mut receiver, borrowed other)
}
```

Each entry is a mode — `borrowed`, `borrowed mut`, or `consumed` — followed
by the name of one of the callable's parameters, or `receiver` for a
method's receiver slot (`50-borrowing.md` §9). Names resolve against the
callable's declaration: an unknown parameter, a name marked twice, or
`receiver` on a function without one is `OAK-P0xxx`-class protocol shape
error (`CodeProtocolShape`). A marked parameter must have a resource type,
which resource resolution checks. Because protocol declarations are
elaborated with the program's internal names, a protocol declared in one
package binds the same contract in every importer — through a qualified
call, an open or selective import, or a sealed signature — so imports and
sealing cannot erase modes. Callable contracts on function-typed
parameters (`50-borrowing.md` §9) have no source spelling yet.

A protocol may also declare **terminal states** (the resolved
`ResourceProtocolDeclaration.Terminal`; source spelling pending with the
other authority spellings): the states an owned resource must reach before
its last name leaves scope (`50-borrowing.md` §9, terminal-state
obligations). The obligation is emitted as the protocol guarantee named
`terminal`, `eventually(S1 or S2 ...)`, so the model checker and the flow
analysis read one fact. Without terminal states the protocol imposes no
obligation.

## 6. What is not derived

Liveness and environment assumptions (fairness, device progress) are the
TLA+ extension module's; the declaration states what may happen, not what
must. Guards and effects beyond the translated subset — loops, calls into
the program, indices computed from other fields — stay in hand-written
models. The declaration does
not generate Lean definitions, state diagrams, or debugger decoding
(constitution: the same fact should eventually drive them).

## 7. Direction

- Typestate-indexed handle types; a source spelling for callable contracts
  on function-typed parameters and for fresh-return facts.
- Conformance checking of a hand-written TLA+ module against the projected
  machine, for modules that predate the declaration.
