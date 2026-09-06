# Oak Language Constitution

## Priorities

Oak makes design trade-offs in this order:

1. **Correctness**
2. **Performance**
3. **Simplicity**

Safety and ergonomics constrain every choice rather than forming lower-priority afterthoughts.

A design is not acceptable merely because it is simpler if it destroys semantic information needed for correctness. A faster design is not acceptable if its invariants cannot be stated and checked. Once correctness and material performance requirements are satisfied, choose the smallest and most orthogonal mechanism.

## Tight surface

Oak should feel lightweight. The language should prefer a small algebra of reusable constructs over a large catalog of special forms.

The core vocabulary is intended to center on:

- functions and expressions;
- records (product types);
- ADTs and eventually GADT-style result refinements (sum types);
- pattern matching;
- generics and constraints;
- phantom/refined semantic types;
- ownership, borrowing, and effects;
- explicit unsafe boundaries.

Domain concepts such as arenas, slabs, handles, encodings, protocols, serializers, intrusive lists, and capabilities should normally be expressible as ordinary types plus semantic facts rather than new syntax.

## One fact, many projections

A semantic fact should have one authoritative representation and be reused wherever possible.

Examples:

```text
field order
  -> type semantics
  -> machine layout
  -> serializer schema
  -> debugger rendering

refinement
  -> type checking
  -> SMT/Lean assumption
  -> runtime check when not statically discharged
  -> generated boundary tests

protocol transition
  -> typestate API
  -> model checker action
  -> DST action
  -> debugger state diagram
```

The compiler must not reconstruct lost facts by guesswork.

## Five semantic axes

Oak separates five orthogonal questions:

1. **Type** — what values mean and which values inhabit the type.
2. **Representation** — what bits/layout encode those values.
3. **Authority / Effect** — what code holding a value may do.
4. **Proposition** — what facts are statically known.
5. **Protocol** — how state may legally evolve.

A feature should not overload one axis to smuggle in another. For example, a documentation tag must not silently alter ABI representation; a payload default must not double as a wire discriminant.

## Safe by default

Safe Oak code must not have undefined behavior from ordinary language operations.

Potentially unsafe operations—raw pointer dereference, unchecked reinterpretation, unproven device/MMIO assumptions, unchecked aliasing, and similar operations—must cross a visible unsafe boundary.

`unsafe` does not disable the type checker. It introduces narrowly scoped assumptions that the compiler cannot establish itself; all unrelated invariants remain checked.

## No hidden work

The language and standard library should make material runtime work visible. In particular, ordinary operations must not silently:

- allocate;
- block;
- perform I/O;
- acquire contended locks;
- invoke unbounded dynamic dispatch;
- copy unbounded data.

Such behavior belongs in explicit effects/APIs.

## Machine semantics are real semantics

Fixed-width integers, overflow behavior, alignment, endianness, pointer width, atomics, volatile/MMIO operations, and layout constraints are part of the language's semantic model rather than backend accidents.

Mathematical integers may exist in proofs/compile-time reasoning, but they must never be silently confused with machine integers.

## Syntax equivalence

Layout-delimited and explicitly braced blocks are two spellings of one syntax tree and one semantics. There is no global syntax mode.

Surface sugar must normalize to a smaller core; it must not create parallel semantics.

## Verification discipline

A formal model proves the model, not automatically the compiler implementation.

For every important feature we track separately:

```text
specified
implemented
unit/property tested
formally modeled
proved
refined to implementation
```

The strongest early refinement targets are foundational laws whose implementation is small enough to relate directly to the model.
