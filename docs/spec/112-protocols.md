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
`receiver` on a function without one is a protocol shape error
(`OAK-M0301`, `CodeProtocolShape`). A marked parameter must have a resource
type, which resource resolution checks. Because protocol declarations are
elaborated with the program's internal names, a protocol declared in one
package binds the same contract in every importer — through a qualified
call, an open or selective import, or a sealed signature — so imports and
sealing cannot erase modes.

### 5.1 The whole `via` clause

The clause carries every fact of a callable's resource contract. Its
grammar, with the callable's own declaration deciding what each name means:

```text
via [unsafe] callable [ '(' entry {',' entry} ')' ] [ ':' result ]

callable := IDENT                  a function declared in the program
          | IDENT '.' IDENT        Type.method — a method of the resource type
entry    := mode IDENT             a resource parameter, or `receiver`
          | IDENT '(' [cmode {',' cmode}] ')' [':' 'fresh']
                                   a callable contract on a function-typed parameter
mode     := 'borrowed' ['mut'] | 'consumed'
cmode    := mode | '_'
result   := 'fresh'                a new authority class no caller name shares
          | 'alias' IDENT          the same class as that argument
          | 'borrow' IDENT {',' IDENT}        a shared borrow of those arguments
          | 'borrow' 'mut' IDENT {',' IDENT}  a mutable reborrow of them
```

```oak
ArenaLifecycle: protocol = {
  resource Arena
  resource Cursor
  initial Open
  make:    Open -> Open   via open(): fresh
  cursor:  Open -> Open   via cursor_of(borrowed a): borrow a
  edit:    Open -> Open   via mut_cursor(borrowed mut a): borrow mut a
  same:    Open -> Open   via peek(borrowed a): alias a
  each:    Open -> Open   via with_each(op(borrowed), borrowed a)
  look:    Open -> Open   via Cursor.read(borrowed receiver)
  release: Open -> Closed via free(consumed a)
  raw:     Open -> Open   via unsafe cursor_raw(borrowed a): alias a
}
```

- **Methods** are spelled `Type.method`, the uniform-call spelling, and
  resolve to the checker's `Type::method` identity; `receiver` in the
  entry list marks the receiver slot (`50-borrowing.md` §9). A bare method
  name is not a callable of the program (`OAK-M0301`).
- **Result identities** are the `: result` clause. Its names must be
  explicit parameters of the callable (identities over the receiver are
  not admitted yet), listed at most once; `alias` takes exactly one. Their
  semantics — validation of the body (`OAK-B0117`), the caller's
  classification, dependency and suspension (`OAK-B0118`, `OAK-B0119`) —
  are those of `50-borrowing.md` §9, and the resolution rules there apply
  unchanged: an alias or borrow names a resource-typed parameter of a
  resource-returning callable, a borrow's origins are `borrowed` or
  `borrowed mut`, a mutable reborrow's origins are all `borrowed mut`.
- **Callable contracts** are the `name(cmode, …)` entries on a
  function-typed parameter. The modes are positional over the parameters
  of the function type, one word per parameter, `_` leaving a position
  unmarked; `: fresh` requires the callable to return fresh authority. A
  contract that marks nothing, one whose count differs from the function
  type's arity, or one on a parameter that is not function-typed is
  `OAK-M0301`. A function value passed for the parameter must carry the
  contract by exact agreement (`OAK-B0116`).
- **`unsafe`** marks the result identity as **trusted**: the compiler
  records the claim and does not validate the body against it
  (`OAK-B0117` is not raised for that callable), so a primitive whose body
  has no tracked provenance — a cursor built over an arena's storage, an
  asm-backed accessor — can state what its result is. Everything else
  about the callable is checked as before: entry authority and retention
  (`OAK-B0114`), exclusivity (`OAK-B0112`), and the caller's reasoning,
  which never depends on whether a claim was validated or trusted. The
  marker requires a result clause (`OAK-M0301`); it is the visible unsafe
  boundary of `00-constitution.md`, recorded in SemIR as the
  `resource.return-trusted` effect beside the identity it trusts, so tools
  and proofs can see where the assumption enters. `Oak.ResourceResult`
  (`spec/lean/Oak/ResourceResult.lean`) states this precisely:
  `Accepted true c p` holds for every body while `Accepted false c p` is
  exactly `Admits c p`, and the caller's classification is definitionally
  independent of the flag.

Every word in a mode or result position must be one of the words above;
anything else is a parse error naming the vocabulary, not a silently weaker
contract downstream. The clause elaborates to the same
`ResourceTransitionDeclaration` facts, callable by callable, that the
compiler's internal declaration path carries, which the tests check by
comparing the two (`compiler/e2e_protocol_via_results_test.go`).

### 5a. Typestate-indexed resources

When a governed resource type is a **record template with one type
parameter**, the protocol puts its state into the handle's type:

```oak
Segment[S]: type = struct { id: u32, generation: u32 }

Custody: protocol = {
  resource Segment
  initial Fresh
  publish: Fresh -> Published via publish(consumed s)
  offload: Published -> Offloaded via offload(consumed s)
  evict: Offloaded -> Evicted via evict(consumed s)
}

publish: (s: Segment[Fresh]): Segment[Published] = Segment { id: s.id, generation: s.generation + u32(1) }
evict: (s: Segment[Offloaded]): Segment[Evicted] = Segment { id: s.id, generation: s.generation + u32(1) }
```

The rules:

1. The projection declares one **marker type per state** (`Fresh: type =
   struct { fresh_: u8 }`, ...), never instantiated as a value, so
   `Segment[Fresh]` and `Segment[Evicted]` are distinct nominal types
   (`20-types.md` §5.1) with one representation (§9, phantom). A program
   that already declares a state's name is `OAK-M0301`.
2. A `via` callable is held to its line: every parameter of the indexed
   type must be `Segment[From]`, a return of the indexed type must be
   `Segment[To]`, a bare `Segment` or a type-variable index is rejected
   (`OAK-M0301`). Calling `evict` on a `Segment[Published]` is therefore an
   ordinary type error, and the legality trap of `custody_next` is
   unreachable from well-typed code (`Oak.Typestate.run_legal`).
3. A transition that consumes one `Segment[From]` and returns
   `Segment[To]` hands back the **same resource in its next state**: its
   result is an alias of the consumed argument by construction
   (`50-borrowing.md` §9, result identity), so the old-state handle is dead
   (`OAK-B0111` on reuse) and nothing is duplicated.
4. A literal of the indexed type — `Segment { ... }`, which takes its type
   arguments from the expected type like a list literal takes its shape
   (`10-syntax.md` §2c), or is an error asking for an annotation — may be
   written anywhere in the **initial state**, and otherwise only inside a
   via callable of a transition **into** that state (`OAK-B0121`). Only the
   transition may make the claim its target state represents.

`Oak.Typestate` (`spec/lean/Oak/Typestate.lean`) states the calculus —
construction at the initial state, transitions along legal lines — and
proves that the machine state always equals the static index
(`run_sound`), that every applied transition is legal (`run_legal`), and
that a handle at a non-initial state can only come from a transition into
it (`construct_initial_or_transition`). Terminal-state obligations and
parameter modes apply unchanged: `Segment` names every instantiation.

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
