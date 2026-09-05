# Oak Semantic Architecture

Oak's central design goal is to define semantic facts once and reuse them everywhere that can benefit from them.

A type, protocol, ownership rule, refinement, effect, or layout fact should not be independently re-written for the compiler, verifier, serializer, debugger, model checker, and documentation. Oak should preserve one checked semantic representation and derive projections from it.

## Core principle

> Define a fact once; project it many ways.

```text
Oak source
    |
    v
parser
    |
    v
typed AST
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

The Semantic IR is the source of truth for all projections.

## Semantic IR responsibilities

The IR must preserve more than ordinary compiler types. It should be able to represent:

- nominal and algebraic type identity;
- fixed-width and mathematical numeric domains;
- record/sum structure;
- exact target representation, size, alignment, offsets, and endianness where specified;
- ownership, borrowing, mutability, and linear/affine state;
- phantom parameters and zero-runtime semantic distinctions;
- refinements and predicates;
- effects and forbidden effects;
- boundedness/resource facts;
- compile-time tags and namespaced metadata;
- protocol states and transitions;
- invariants, preconditions, and postconditions;
- temporal assumptions and guarantees;
- source locations and documentation.

Not every type needs every category.

## Types drive multiple projections

Example:

```oak
IrqId[N]: type = u16
  where value < N

Irq: type =
  enabled: bool
  priority: u8
  latched_pending: bool
  level_asserted: bool
  active: bool
```

The same semantic declarations should be sufficient to derive:

- the machine representation;
- bounds checks or their elimination when statically proved;
- Lean definitions;
- SMT assumptions/obligations;
- structured debugger descriptions;
- serialization schemas where requested;
- property-test generators;
- human-readable documentation.

## Machine integers and mathematical integers are different

Oak must never silently identify an unbounded mathematical integer with a machine integer.

Examples:

```text
Nat / Int       mathematical domains
u8..u64         fixed-width machine domains
uint / int      target-word machine domains
uptr / ptr      target-pointer-width machine domains
```

Conversions are explicit semantic operations with explicit proof obligations where overflow or truncation is possible.

This lets proofs reason accurately about wrapping, checked arithmetic, address widths, wire layouts, and target-specific representation.

## Layout is a semantic fact

Machine layout is not merely a backend implementation detail.

For a representation-constrained type, the compiler should be able to expose facts such as:

```text
size(T)
align(T)
offset(T.field)
endianness(T.field)
```

These facts should be consumable by verification and tooling.

A wire or MMIO layout can therefore use the same checked type definition as executable code rather than maintaining a duplicate schema.

## Refinements

Oak should support refinements as semantic predicates over values.

Conceptual syntax:

```oak
PageIndex[N]: type = u32 where value < N
AlignedPage: type = uptr where value % PageSize == 0
```

The exact syntax remains open. The semantic requirement does not: a refinement becomes a fact available to the type checker, SMT solver, Lean projection, optimizer, test generator, and documentation.

## Ownership and typestate

Ownership is part of semantics, not linting.

Examples:

```text
CpuOwned[Buffer]
DeviceOwned[Buffer]
SharedRead[Buffer]
```

A DMA submission may be modeled as a transition:

```text
CpuOwned[Buffer] -> DeviceOwned[Buffer]
```

and completion as:

```text
DeviceOwned[Buffer] -> CpuOwned[Buffer]
```

The executable checker prevents illegal use, while protocol/state projections can reason about the same transitions globally.

## Effects

Effects should be explicit enough to express systems constraints.

Conceptual examples:

```oak
fn irq_entry(...)
  effects { CpuLocal, Mmio[Aic] }

realtime fn process(...)
  effects { AudioRead, AudioWrite }
  forbids { Allocate, Block, Syscall }
```

The exact syntax remains open.

Effects should power:

- compile-time capability restrictions;
- realtime/no-allocation guarantees;
- call-graph checks;
- proof assumptions;
- documentation;
- security review.

## Protocols and temporal semantics

Executable functions describe what one step does. Concurrent systems also need a description of which sequences of steps are legal.

Oak should therefore support protocol/state-machine declarations with a semantics capable of projection into temporal/model-checking tools.

Conceptual example:

```oak
protocol VirtualIrq
  state Idle
  state Pending
  state Active

  transition inject Idle -> Pending
  transition acknowledge Pending -> Active
  transition eoi Active -> Idle

  invariant active_is_known_irq
```

The same declaration should eventually be able to drive:

- typestate APIs;
- state-machine implementation scaffolding;
- model checking;
- Lean transition definitions;
- deterministic simulator actions;
- state diagrams;
- debugger decoding.

Temporal liveness properties must state environmental assumptions explicitly. For example, eventual completion may depend on scheduler fairness, device progress, or peer behavior.

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

All backends consume the same Semantic IR rather than independent hand-written models whenever possible.

## Proof status is explicit

Oak tooling should distinguish at least:

- **specified**: a property exists in the semantic model;
- **checked**: discharged by ordinary static checking;
- **proved-smt**: discharged by an SMT solver;
- **proved-kernel**: checked by a proof assistant kernel;
- **model-checked**: explored by a finite-state/temporal checker under stated bounds;
- **tested**: exercised against generated or user tests;
- **refined**: a formal correspondence to a lower-level implementation/model has been established.

The compiler and documentation must never collapse these into a vague "verified" label.

## Tags remain extensible metadata

Oak's existing compile-time tag system remains useful for metadata that does not change core language semantics:

```oak
field: u64 `{ wire.field: 7, ui.unit: "bytes" }`
```

Correctness-critical concepts such as ownership, effects, refinements, alignment, and protocol transitions should graduate to typed language constructs rather than relying on arbitrary stringly metadata.

## Syntax and semantics are separate

Oak supports both layout and explicit-brace styles. Both normalize into one AST before semantic analysis.

No proof, type rule, ownership rule, effect, or backend may depend on which surface style was used.

See `SYNTAX_DIRECTION.md`.

## Development strategy

Oak should earn these features incrementally using real systems code as pressure.

Recommended sequence:

1. dual layout/explicit block syntax;
2. stable Semantic IR for existing Oak types, tags, ownership, views/spans, and layout;
3. one multi-projection experiment using the OS interrupt types;
4. refinements and SMT obligations;
5. Lean projection for local invariants;
6. protocol/state-machine representation and temporal projection;
7. generated property/DST tests;
8. effects and bounded/realtime contracts;
9. stronger refinement between generated/executable code and proof models.

The OS remains implemented in Zig while Oak proves that its semantic model can eliminate duplication around real core subsystems. Oak should replace the implementation language only if and when its generated code, machine control, ergonomics, and verification story are demonstrably better.