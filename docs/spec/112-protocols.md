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
  — one transition line. The guard is a Bool expression over `data.field`,
  `data.field[i]` and `data.field[i].sub` reads (an array of records: the
  element type is a declared record), the payload, and the **quantifier
  forms** below; the effects are statements over `data.field = e`,
  `data.field[i] = e` and `data.field[i].sub = e` and the payload. Both use
  ordinary Oak and are checked by every gate once projected.
- Quantifier forms over a fixed array field: `count(data.f)` (`u32`, the
  number of true slots of an `[N]Bool` field), `all(data.f)`,
  `any(data.f)`, `none(data.f)`, and over an array of records
  `count(data.peers, acked)`, `all(data.peers, acked)`,
  `any(data.peers, acked)`, `none(data.peers, acked)`, where the second
  argument names a `Bool` field of the element record. Each distinct use
  projects one bounded helper (`name_count_acks: (data: NameData): u32`,
  a `while` over the array) that the guard calls, so the Oak gate sees a
  plain fold; the model-checker module writes `Cardinality({k \in 0..N-1 :
  f[k]})` (adding `FiniteSets`) and the bounded `\A`/`\E`. A quorum guard
  is therefore declared once — `commit: Normal -> Normal when
  count(data.acks) >= u32(2)` — and both gates read it. `Oak.ProtocolQuorum`
  fixes the shared meaning over a Bool vector: `count ≤ N`; `all`, `any`,
  `none` are exactly `count = N`, `count > 0`, `count = 0`; acknowledging
  a slot never lowers the count (`quorum_stable`). Shape errors
  (`OAK-M0301`): a form over a field `data` does not declare, over a
  non-array field, a one-argument form over non-`Bool` elements, a
  two-argument form whose element is not a declared record or whose named
  field is not `Bool`. Multi-field payloads per step remain one scalar
  (the typed-command derive admits one); a record payload is a follow-up. An index is checked at
  run time like any Oak index, so a guard that indexes by the payload
  bounds it first (`u32(who) < u32(2) && data.parked[u32(who)]`); the
  model-checker module gets the same conjunct and a payload domain that
  matches.

- `fair step` and `strongly fair step` — a fairness assumption on one step
  name: every line of the step, its payload quantified. The model-checker
  module conjoins `WF_vars(Step)` or `SF_vars(Step)` to `Spec` (§4); the
  projection into Oak reads neither, since fairness is a claim about the
  environment, not about the program.
- `eventually target` and `eventually from -> target` — a liveness
  property, where each side is a state name or a `Bool` expression over
  `data` in the guard subset: `eventually Yielded`, `eventually Running ->
  Yielded`, `eventually Running -> data.budget == u32(1)`. The module
  states them as `<>` and `~>` (leads to) under the property `Liveness`,
  which TLC checks against the declared fairness, and `oak prove` decides
  them itself for a finite machine (`125-verification.md` §2b), over the
  reachable states of the projection. Each side is also projected as a
  Bool predicate over the state and data (`name_live1_from`,
  `name_live1_to`, ...). A state no transition reaches, an unknown step,
  or data in a protocol that declares none is a shape error
  (`OAK-M0301`).

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

### 2a. Lowering: the declaration dictates the code

A machine without a `data` record is lowered by the C backend from a
**transition table the compiler computes from the declaration**
(`90-backend.md` §14); the Oak projections above remain its meaning for
the interpreter and the Lean extraction, and the backend's code is proved
to compute the same function (`Oak.Protocol`). The symbols of the table
are the step tags — a payload no guard reads leaves its step one symbol —
or, for a machine with exactly one step whose `u8` payload guards read, the
256 payload values: every guard is evaluated at compile time for every
value, so a byte-driven machine (a UTF-8 validator, a tokenizer) becomes a
table indexed by the input byte. A guard outside the evaluator's vocabulary
(the payload, literals, width conversions, `+ - * / %`, comparisons,
`&& || !`) leaves the branch-tree projection in place.

Two forms, chosen by the machine's size and never by the program's use:

| Form | When | `next` | `legal` |
| --- | --- | --- | --- |
| shift DFA | states plus the sink at most ten | `(rows[symbol] >> state) & 63`: one load, one shift, one mask | the same, compared with the sink |
| dense table | otherwise, up to 254 states and 64 KiB | `table[state][symbol]`: one load | one load, one compare |

Under the shift form the state type's tags are the field offsets `6 * i`
(`ADTType.TagValues`), a representation choice matching compares by name
and nothing else observes. The sentinel is the sink, one past the last
state; `next` traps on it exactly where the branch tree asserted.

A byte-driven machine also projects **`name_run`**:

```oak
utf8_run: (state: Utf8State, bytes: []u8): Utf8State
```

which steps the whole view with the sink absorbing and checks once at the
end: it ends in the declared final state when every step was legal and
traps when any was not — `Oak.Protocol.runSink_correct` — so the loop body
carries no branch. Measured on the UTF-8 validator below, the emitted code
runs at the speed of the hand-written shift DFA it is modeled on
(`benchmarks/state-machines/`).

Payload guards without a data record are honored: `legal` is the
disjunction of the step's lines whose source state and guard hold, and
`next` takes the first such line, in declaration order — the same
first-match rule as the data-carrying projection. (Until 2026-09-12 the
projection dropped these guards; the byte-driven shape below did not work.)

```oak
Utf8: protocol = {
  initial Accept
  byte(b: u8): Accept -> Accept when b < u8(128)
  byte(b: u8): Accept -> Two when b >= u8(194) && b <= u8(223)
  byte(b: u8): Two -> Accept when b >= u8(128) && b <= u8(191)
  ...
}
```

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
`Spec`. Guards and effects translate from the subset a line may use: field,
element and element-field reads (`peers[i].acked`), the payload, literals,
width conversions, `+ - * / %`, comparisons, `&& || !`, the quantifier
forms (`Cardinality({k \in 0..N-1 : f[k]})` with `EXTENDS FiniteSets`,
`\A k \in 0..N-1 : f[k]`, `\E`, and `~f[k]` under `\A` for `none`),
`data.field = expr`, `data.field[i] = expr` and `data.field[i].sub = expr`
(element and element-field stores on one array fold into one
`[field EXCEPT ![i] = v, ![j].sub = w, ...]`); an `[N]T` field is a
function `[0..N-1 -> T]`, initialized as one arrow when every element
agrees and as a `CASE` otherwise, and an element record `R` is the record
set `[f1: D1, f2: D2]` from the program's declaration (`oak protocol -tla`
reads it from the same file; `ProtocolTLAWithRecords` takes it);
anything else stops the export naming the line. The module is complete for what the declaration says and
checkable as is (TLC checks the modules of both examples above). Declared
fairness joins `Spec` — `Spec == Init /\ [][Next]_vars /\ WF_vars(Tick) /\
SF_vars(Resume)`, a payload step as `WF_vars(\E on \in On : Signal(on))` —
and declared liveness is the property `Liveness`, one conjunct per entry:
`<>(state = "Yielded")`, `((state = "Running") ~> (state = "Yielded"))`, a
data side through the same translation as a guard. `oak protocol -tla Name
-cfg out.cfg` also writes the TLC configuration: `SPECIFICATION Spec`,
`INVARIANT TypeOK`, `PROPERTY Liveness` when the declaration states one,
and a small domain per payload constant (`{TRUE, FALSE}`; `{0, 1, 2, 3}`
for a scalar) to widen as the model needs. Scenarios extend the module for
environment assumptions beyond the declared fairness in a module of their
own, so regenerating never overwrites hand-written properties. The
generated header names the source it came from. Conformance (§4a)
compares the machine and skips `Spec` and `Liveness`.

## 4a. Conformance of a hand-written module

```text
oak protocol -conform Name -against Custody.tla [-json] file.oak
```

A module written before the declaration, or kept beside it for the
properties it states, must agree with the projection — and the checker,
not a reviewer, says whether it does. Both texts are read into the
projection's **normal form**: constants, variables, `States`, `Init` as a
set of conjuncts, one action per step with one disjunct per line — each a
conjunction of `state = "From"`, guard terms, `state' = "To"`, primed
assignments (`EXCEPT` forms included) and `UNCHANGED` — `Next` as a set of
disjuncts, and `TypeOK`. Spellings that differ only in whitespace,
redundant parentheses, conjunct or disjunct order, or comments are the
same line; a guard compares by its canonical text, so `who < 2` and
`(who) < 2` agree and `who < 3` does not. The report names every
difference with its kind, action and disjunct: a missing or extra action,
a missing or extra line (with the closest line on the other side, so a
changed guard, target or effect shows what it was changed from), and
`Init`, `TypeOK`, `Next`, constants, variables or states that differ.
Exit 0 means agreement; 1 a difference or an unsupported form; `-json`
prints the report as data.

What the reader does not understand it reports as **unsupported** by line
— a disjunct without the state conjuncts, a quantifier outside a guard, a
definition it cannot place — and never judges: for such modules **TLC
refinement is the check, and the tool runs it**. When the report has an
unsupported form (or on `-tlc`, for any module), the projection is written
as a module of its own, `<Name>Projection`, and a refinement module
`<Module>Refinement` extends the hand-written module, instantiates the
projection under the state mapping — `INSTANCE <Name>Projection WITH state
<- state, count <- n` (`-map state=st,...` renames; unmapped variables
keep their names and must be declared by the module) — and states
`RefinementSpec == Projection!Spec`; its configuration is `SPECIFICATION
Spec`, `PROPERTY RefinementSpec`, the module's own constant values from
`-against-cfg module.cfg`, and the projection's payload domains at their
defaults unless the module declares the same constant. TLC then decides
whether **every behavior of the hand-written module is a behavior of the
projection**: "No error has been found" is agreement (exit 0); a violated
action property is a behavior the projection does not admit, reported with
TLC's counterexample (exit 1); and without a Java runtime and
`tla2tools.jar` (`OAK_JAVA`, `OAK_TLA2TOOLS_JAR`, or
`~/.cache/tla2tools/tla2tools.jar`) the four files wait in the directory
the report names (`-out dir` to choose it), exit 2. A set-and-function
module — `Parked == {k \in 0..1 : parked[k]}`, `Halt == ... Parked = 0..1
...` — is thereby checked against the same projection the normal form
reads, and a module that halts one parked slot early is caught at the
`Halt` step (`compiler/protocol_refine_test.go`). Helper operators
inlined in the hand-written module compare as their expanded guard text
only when the projection spells the same text; a module that names a
quorum predicate of its own is therefore reported as a guard difference,
which is honest (the checker compares what the two texts say), and the
quantifier forms of §1 exist so that the projection can say it too.

`Oak.ProtocolConformance` (`spec/lean/Oak/ProtocolConformance.lean`)
states what the verdict means: two machines with the same line sets have
the same step relation under every interpretation of guards and effects
(`steps_of_lines`), and with the same initial states reach the same states
(`conform_reachable_equal`); the report is complete — a line on one side
only is a reported line, and an empty report means the line sets agree
(`report_complete`, `empty_report_agrees`).

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

A typestate resource may also carry **region parameters**
(`50-borrowing.md` §8c): `Node[R, S]: type = struct { data: View[f32, R],
n: u32 }` with `initial Lazy` and `realize: Lazy -> Realized` gives
`realize[R]: (x: Node[R, Lazy]): Node[R, Realized]`, the same borrows in
the next state, and an operation that needs its operand in storage takes
`Node[R, Realized]` — a wrong order is a type error, not a run-time trap
(ml F7). Region parameters are erased before the state is applied, so
each state's instantiation borrows exactly as the template declares.

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

Environment assumptions beyond fairness on the declared steps (device
progress, timing) are the TLA+ extension module's. `oak prove` decides
safety invariants (`125-verification.md` §2a) and, for a finite machine,
the `eventually` entries under the declared fairness (§2b) — over the
projection's reading, the first line whose guard holds; TLC checks the
same entries over the declaration's every-line reading. Guards and effects beyond the translated subset — loops, calls into
the program, indices computed from other fields — stay in hand-written
models. The declaration does
not generate Lean definitions, state diagrams, or debugger decoding
(constitution: the same fact should eventually drive them).

## 7. Direction

- Typestate-indexed handle types; a source spelling for callable contracts
  on function-typed parameters and for fresh-return facts.
- Conformance of modules outside the normal form (helper operators,
  quantifiers outside guards): a semantic comparison through TLC
  refinement driven by the checker, rather than the textual normal form of
  §4a.
