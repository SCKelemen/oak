# Functional Ergonomics, Systems Cost Model

Oak aims for the day-to-day ergonomics of ML-family languages, Elm, and the best parts of TypeScript tooling, while preserving the runtime cost model of Zig/C.

This is a semantic requirement, not a marketing analogy.

## Functional surface

Oak should make these patterns natural:

- expression-oriented functions and blocks;
- local type inference;
- algebraic data types;
- exhaustive pattern matching;
- generic functions and types;
- small pure functions;
- immutable/read-only views by default;
- explicit mutation where mutation is the clearest model;
- first-class function values when their representation/capture cost is known;
- structural interface/constraint satisfaction for generic ergonomics;
- strong editor/compiler feedback with exact source locations.

The common case should not require repetitive type annotations, constructor qualification, lifetime syntax, or ceremony that the compiler can infer unambiguously.

## Systems cost model

Ergonomic abstraction must not imply a hidden runtime system.

Oak has no mandatory:

- garbage collector;
- hidden heap allocation;
- implicit boxing;
- exception unwinding runtime;
- runtime interface vtables for ordinary generic constraints;
- reference counting;
- hidden asynchronous scheduler;
- implicit buffer copying.

A language feature that requires one of these costs must make that representation/effect explicit.

## Expressions do not imply allocation

Expression-oriented code lowers to ordinary control flow.

```oak
result := value ?
  | .Some(x) => x + 1
  | .None    => 0
```

should normally lower to a tag test plus branches and scalar operations. The expression-oriented syntax is not permission to materialize temporary heap objects.

## ADTs are concrete values

ADTs have a statically known representation chosen by the representation layer. A conventional closed ADT can lower to:

```text
tag + maximum payload storage
```

or to a smaller representation when a proof-preserving representation optimization applies.

Pattern matching should lower to direct tag/literal tests and branches. Exhaustiveness is compile-time information.

## Generics specialize by default

Generic constraints are compile-time predicates. Executable lowering should normally specialize/monomorphize generic code so that:

```oak
fn max[T: Ord[T]](a: T, b: T): T
```

can become direct operations on the chosen concrete `T` without an implicit interface object.

Code-size trade-offs from specialization are real and may later admit explicitly selected alternatives, but dynamic dispatch is never silently introduced just to implement a generic constraint.

## Function values and closures

Plain function values may use a direct function pointer representation.

A capturing closure conceptually contains:

```text
code pointer + environment
```

The environment's storage/lifetime must be established explicitly by ownership analysis. Capturing a local variable must not silently heap-promote that variable.

A closure is legal when its environment can be represented safely using known storage, such as:

- stack lifetime that does not escape;
- caller-owned storage;
- an explicit arena/region;
- static storage;
- another explicit owner.

If escape requires allocation, that allocation is an effect and must be explicit/allowed.

## Iterators and functional combinators

Libraries may offer `map`, `filter`, folds, iterators, and pipelines, but their semantics must preserve the cost model.

For bounded/slice-like inputs, optimized lowering should be capable of producing a simple loop with no intermediate allocation when the abstraction is statically known.

APIs that inherently construct new storage must accept or identify their allocator rather than allocate invisibly.

## Mutation is explicit, not stigmatized

Oak is not purely functional. Mutation is appropriate for:

- state machines;
- parsers/lexers;
- DMA buffers;
- intrusive structures;
- realtime DSP;
- device drivers;
- bounded in-place algorithms.

The language should make mutation locally obvious and ownership-safe, while keeping pure computation easy to recognize and reason about.

## TypeScript-inspired ergonomics without JavaScript semantics

Useful TypeScript-like qualities include:

- excellent language-server discoverability;
- lightweight local inference;
- structural satisfaction of compile-time interfaces;
- fast incremental feedback;
- easy navigation/refactoring;
- precise diagnostics.

Oak does not inherit JavaScript's dynamic object model, implicit coercions, boxed values, prototype semantics, or GC cost model.

## Elm/ML-inspired ergonomics without mandatory persistent allocation

Useful ML/Elm qualities include:

- ADTs as ordinary design vocabulary;
- matching as the primary way to consume sums;
- expression-oriented APIs;
- inference that removes annotation noise;
- pure functions as the easy/default reasoning unit.

Oak does not require persistent heap data structures or a garbage-collected runtime to obtain those ergonomics.

## Performance transparency

For core language constructs, a competent systems programmer should be able to predict the broad machine shape from the Oak source:

```text
record          -> fields in known storage
ADT             -> tag/payload representation
match           -> tests/branches
specialized fn  -> direct call/inlined code
view/span       -> pointer + length (subject to target representation)
raw pointer     -> machine pointer
arena/slab op   -> explicit bounded allocator operation
```

When that correspondence is not obvious, compiler tooling should expose the lowering rather than rely on folklore.
