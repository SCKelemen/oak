# Oak Semantic Architecture

Oak's central design goal is to define semantic facts once and reuse them everywhere that can soundly benefit from them.

> Define a fact once; project it many ways.

The normative language model is organized around five orthogonal axes described in `LANGUAGE_MODEL.md`:

1. **Type** — what does this value mean?
2. **Representation** — what bits represent it?
3. **Authority / effects** — what may code holding it do?
4. **Proposition** — what facts are statically known?
5. **Protocol** — how may state evolve over time?

These axes are kept separate deliberately. Two values may share representation but have different semantic types. A type may have propositions without constraining layout. A protocol can refer to authority transitions without baking scheduler policy into the type.

```text
Oak source
    |
    v
parser / layout normalization
    |
    v
typed syntax
    |
    v
Semantic IR
    |
    +--> executable lowering / C / native backend
    +--> machine layout / ABI metadata
    +--> serialization and wire schemas
    +--> debugger metadata
    +--> documentation / UI schemas
    +--> SMT proof obligations
    +--> Lean definitions and theorem skeletons
    +--> temporal/state-machine models
    +--> property-test generators
    +--> deterministic simulation actions
```

The Semantic IR is the semantic source of truth for all projections.

## Current executable foundation

The Go package `semir` is the first executable representation of this design. It deliberately starts smaller than the eventual language:

- `Definition` contains the five axes independently;
- proposition expressions are structured trees, not strings;
- temporal formulas are structured trees;
- proof status is explicit;
- authority validation rejects contradictory effect contracts;
- protocol validation rejects missing states and malformed transitions;
- representation validation rejects impossible alignment claims;
- module validation rejects duplicate definitions/protocols and unknown protocol references.

The current `semir` package is a host compiler data model, not yet a promise that every proposed Oak surface syntax exists. Surface syntax should be added only after its semantic meaning is stable in the IR.

## Type axis

The type axis preserves:

- nominal and algebraic type identity;
- fixed-width and mathematical numeric domains;
- record/product structure;
- sum/ADT structure;
- functions;
- generic constraints;
- phantom parameters and zero-runtime semantic distinctions.

Example:

```oak
IrqId[N]: type = u16
  where value < N
```

`IrqId[N]` is not merely an alias for `u16`; it is a semantic type whose machine representation may be `u16` and whose proposition axis contains `value < N`.

## Representation axis

Machine layout is not merely a backend implementation detail. A representation-constrained definition may expose:

```text
bits(T)
size(T)
align(T)
offset(T.field)
endianness(T.field)
tag-layout(T)
```

These facts should be consumable by verification and tooling.

A wire/MMIO/ABI type can therefore use the same checked definition as executable code rather than maintaining a duplicate schema.

### Unknown representation stays unknown

The IR must fail closed when earlier compiler phases lost information. It must never invent semantic facts for convenience.

For example, Oak's historical AST stores record fields in a Go map. Exact source field order therefore cannot yet be justified from that node. Semantic record membership can be projected; exact machine field layout must remain unspecified until the syntax/typed representation preserves order.

This is intentional: missing information is represented as missing information, not reconstructed by guesswork.

## Machine integers and mathematical integers are different

Oak must never silently identify an unbounded mathematical integer with a machine integer.

```text
Nat / Int       mathematical domains
u8..u64         fixed-width machine domains
uint / int      target-word machine domains
uptr / iptr     target-pointer-width machine domains
```

Conversions are explicit semantic operations with explicit proof obligations where overflow or truncation is possible.

## Authority and effects

Ownership is part of semantics, not linting.

Examples:

```text
CpuOwned[Buffer]
DeviceOwned[Buffer]
SharedRead[Buffer]
UniqueWrite[Buffer]
```

DMA submission may be modeled as:

```text
CpuOwned[Buffer] -> DeviceOwned[Buffer]
```

and completion as:

```text
DeviceOwned[Buffer] -> CpuOwned[Buffer]
```

Effects express systems constraints:

```oak
fn irq_entry(...)
  effects { Cpu.Local, Mmio.Aic }

realtime fn process(...)
  effects { Audio.Read, Audio.Write }
  forbids { Memory.Allocate, Thread.Block, Os.Syscall }
```

Required and forbidden effects must be internally consistent. The same effect cannot be both.

`unsafe` is an explicit authority/proof boundary, not a switch that disables all checking.

## Proposition axis

Refinements, preconditions, postconditions, and invariants are structured propositions.

Conceptual examples:

```oak
PageIndex[N]: type = u32 where value < N
AlignedPage: type = uptr where value % PageSize == 0
```

A proposition becomes one fact available to:

- the type checker;
- SMT;
- Lean projection;
- optimizer/bounds-check elimination;
- test generation;
- documentation.

The `semir.Expr` tree exists specifically so proof backends do not have to parse arbitrary annotation strings.

## Protocol axis

Executable functions describe what one step does. Concurrent systems also need a description of which sequences of steps are legal.

Conceptual example:

```oak
protocol VirtualIrq
  state Idle
  state Pending
  state Active

  transition inject Idle -> Pending
  transition acknowledge Pending -> Active
  transition eoi Active -> Idle
```

The same declaration should eventually drive:

- typestate APIs;
- executable state-machine scaffolding;
- model checking;
- Lean transition definitions;
- deterministic simulator actions;
- state diagrams;
- debugger decoding.

Temporal liveness properties must state environmental assumptions explicitly. Eventual completion may depend on scheduler fairness, device progress, or peer behavior.

The `semir.TemporalExpr` tree is the shared representation for these formulas; temporal backends should consume that rather than independent handwritten models whenever possible.

## Verification backends have different jobs

Oak should not pretend one solver is ideal for every property.

```text
ordinary type facts       -> type checker
ownership/linearity       -> ownership checker
arithmetic refinements    -> SMT
finite state protocols    -> model checker
mathematical theorems     -> Lean / interactive proof
implementation behavior   -> generated property tests / DST
unproved debug contracts  -> runtime assertions where requested
```

All backends should consume the same Semantic IR facts where possible.

## Proof status is explicit

Oak tooling distinguishes at least:

- **specified** — property exists in the semantic model;
- **checked** — discharged by ordinary static checking;
- **proved-smt** — discharged by an SMT solver;
- **proved-kernel** — checked by a proof assistant kernel;
- **model-checked** — explored by a finite-state/temporal checker under stated bounds;
- **tested** — exercised against generated or user tests;
- **refined** — formal correspondence to a lower-level implementation/model has been established.

The compiler and documentation must never collapse these into a vague `verified` label.

## Tags remain extensible metadata

Oak's existing compile-time tags remain useful for projection metadata that does not define core language correctness:

```oak
field: u64 `{ wire.field: 7, ui.unit: "bytes" }`
```

Correctness-critical concepts such as ownership, effects, refinements, alignment, discriminants, and protocol transitions graduate to typed language constructs and typed Semantic IR nodes.

## Existing Oak features map naturally

```text
ADTs / records / generics               -> Type
machine ints / pointers / layouts       -> Representation
views / spans / borrow checker / unsafe -> Authority
phantom types / constraints             -> Type + Proposition
struct tags                             -> extensible attributes
pattern-driven state changes            -> seed for Protocol
```

The architecture extends Oak's strongest existing ideas rather than replacing them.

## Strings and validity

Encoding is a semantic validity fact. Arbitrary bytes cannot safely become `Str[Utf8]` merely by attaching a phantom encoding parameter.

A future safe API should distinguish raw bytes from validated strings and make validation/unsafe assumption explicit.

## Interfaces

Interface constraints are compile-time capabilities by default and should not imply hidden vtables or allocation. Runtime existential/interface values, if added, must have explicit type and representation semantics.

## C is one projection

Readable C remains a valuable bootstrap backend and audit surface, but Oak semantics are not defined by C. The Semantic IR is above executable backends and proof/tooling projections alike.

## Syntax and semantics are separate

Oak supports both layout and explicit-brace styles. Both normalize into one parser path before semantic analysis.

No proof, type rule, ownership rule, effect, representation, or protocol may depend on which surface style was used.

See `SYNTAX_DIRECTION.md`.

## Development sequence

1. stabilize dual layout/explicit block syntax;
2. establish the five-axis Semantic IR and validation rules;
3. preserve enough typed/source structure to derive existing Oak definitions without information loss;
4. perform one multi-projection experiment using OS interrupt types;
5. add refinements and SMT obligations;
6. add Lean projection for local invariants;
7. add protocol/state-machine syntax and temporal projection;
8. generate property/DST tests;
9. add effects and bounded/realtime contracts;
10. strengthen refinement between executable lowering and proof models.

The OS remains implemented in Zig while Oak proves that its semantic model can eliminate duplication around real core subsystems. Oak should replace the implementation language only if and when its generated code, machine control, ergonomics, and verification story are demonstrably better.
