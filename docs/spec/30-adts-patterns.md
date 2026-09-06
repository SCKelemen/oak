# ADTs and Pattern Matching

This document is normative for Oak algebraic data types and matching. Recursive coverage, redundancy, reachable-state analysis, counterexample generation, and GADT-ready refinement coverage are specified in `35-pattern-analysis.md`.

## 1. Closed nominal sums

A declaration such as:

```oak
Option[T]: type =
  | Some: T
  | None
```

defines one closed nominal sum type `Option[T]` with constructors `Some` and `None`.

A bare constructor has Unit payload. A payload-bearing constructor has exactly the payload type written after `:`.

ADTs are not ordinary untagged unions. The constructor identity/tag is part of the semantic value.

## 2. Construction

Canonical qualified form:

```oak
Option.Some(42)
Option.None
```

Context-inferred shorthand:

```oak
x: Option[i32] = .Some(42)
y: Option[i32] = .None
```

The shorthand is accepted only when the expected ADT is uniquely determined.

## 3. Payload defaults

A constructor may define a default payload:

```oak
Comparison: type =
  | Less:    i8 = -1
  | Equal:   i8 = 0
  | Greater: i8 = 1
```

The right-hand side after `=` means **payload default only**.

It does not mean:

- runtime discriminant;
- C enum numeric value;
- wire code;
- serializer tag;
- arbitrary metadata.

Those are separate representation/metadata facts.

When an inferred-default form is retained, `:= expr` means exactly “infer this constructor payload type from `expr`.”

```oak
Comparison: type =
  | Less    := -1
  | Equal   := 0
  | Greater := 1
```

This is type-inference sugar, not a new ADT category.

Whether an explicitly supplied payload may override a constructor default is not yet normative. The compiler should not silently invent override semantics.

## 4. Pattern algebra

The core pattern language is deliberately small:

```text
_                  wildcard
x                  binding
literal            literal equality
.Case              constructor without payload
.Case(pattern)     constructor with payload pattern
```

Nested constructor patterns compose recursively.

Record destructuring may extend the same algebra later rather than adding a parallel pattern system.

Typed binding annotations are optional where inference is complete and may be used where they constrain or document an otherwise ambiguous match.

## 5. Match expression

```oak
value ?
  | .Some(x) => x
  | .None    => fallback
```

Evaluation semantics:

1. evaluate the scrutinee exactly once;
2. consider arms in source order;
3. choose the first matching arm;
4. evaluate only that arm;
5. the selected arm's value is the value of the whole match expression.

The right side of an arm is an expression and may be a block expression.

## 6. Branch typing

Every reachable arm result must be compatible with a common result type.

The type checker may compute that common type using its semantic join operation. It must not silently introduce runtime boxing or `any` simply to force unrelated branch types to agree.

When no safe representable common type exists, the match is ill-typed unless the programmer explicitly requests an appropriate sum/dynamic representation.

`never` arms participate naturally: a non-returning arm does not force the other arms to widen.

## 7. Exhaustiveness

A match over a closed ADT must be exhaustive over its reachable semantic case space.

Coverage is recursive through constructor payload patterns; seeing a constructor name does not by itself imply the constructor's entire payload space is covered. `35-pattern-analysis.md` defines the complete coverage/usefulness rules and source-level counterexamples.

A missing reachable case is a compile-time error.

For large scalar domains such as `u32` or strings, finite literal arms are not exhaustive without a wildcard/binding remainder.

Redundant and refinement-impossible arms are diagnosed.

## 8. Constructor narrowing

Inside a constructor arm, the scrutinee is known to be that constructor and payload bindings have the constructor's payload type/refinement.

Conceptually:

```oak
x: Option[T]

x ?
  | .Some(v) => ... // v: T
  | .None    => ...
```

For GADT-style constructors, matching may additionally introduce constructor-specific propositions/equalities into the arm's proof context. Those facts restrict the reachable semantic case space described by `35-pattern-analysis.md`.

This extends ordinary ADT matching rather than creating separate GADT match syntax.

## 9. Indexed ADTs and constructor results

Oak models GADTs as ordinary closed ADTs whose constructors may state a more
specific result application:

```oak
Expr[T]: type =
  | Int: i64   => Expr[i64]
  | Flag: Bool => Expr[Bool]
  | Id: T      => Expr[T]
```

The clause after `=>` is the constructor result. It must name the enclosing
ADT and supply exactly one index for each declared type parameter. A constructor
without an explicit result implicitly returns the enclosing ADT applied to its
parameters in declaration order.

Constructor checking unifies the declared result indices with the expected ADT
application. A fixed index creates an equality requirement. The first occurrence
of a result parameter binds it; repeated occurrences require the same semantic
type. Failure means that constructor cannot inhabit the expected indexed type.

Matching a reachable constructor introduces the solved equalities into that
arm's proof context. Constructors whose result equations are contradictory are
excluded from the reachable case set, so their arms are semantically `never`
and are not required for exhaustiveness.

The initial solver is intentionally equality-only. General propositions,
arithmetic indices, existential indices, and user-directed proof terms require
separate normative extensions. They must not be inferred by ad hoc runtime tags.

## 10. Representation separation

The semantic ADT does not prescribe one fixed ABI.

A representation pass may choose a conventional tag + payload layout or a smaller equivalent representation if it can preserve the semantic constructor distinction and all observable operations.

Compile-time metadata/default values do not silently become representation discriminants.

## 11. Metadata separation

Legacy documents sometimes overloaded constructor defaults/literals as protocol codes, human labels, or static lookup metadata. Those concepts are separated now.

Conceptually:

```oak
Status: type =
  | NotFound: StatusPayload = defaultPayload
      @wire.code(404)
      @doc.label("Not Found")
```

The precise attribute syntax is defined by the metadata spec; the important semantic rule is that payload, representation, and metadata are distinct axes.

## 12. Runtime typecase

A pattern such as:

```oak
x: any
x ?
  | n: i32 => ...
```

requires an explicit runtime representation for `any`/type identity. It is not part of the core pattern language until that representation is specified. Static type narrowing in generic/proof contexts does not imply runtime RTTI.

## 13. Formal verification targets

Formal obligations include:

- constructor and nested-payload coverage/exhaustiveness;
- redundancy/usefulness over source-ordered arms;
- refinement-restricted reachable case spaces and impossible arms;
- counterexamples are reachable and uncovered;
- match selection is deterministic;
- only the selected branch is evaluated;
- constructor narrowing yields the declared payload type/refinement;
- `never` branches do not widen a match result;
- erased proof/index information does not alter runtime constructor semantics.

`Oak.Exhaustiveness` formalizes the initial finite-constructor laws. `Oak.PatternAnalysis` formalizes reachable-case coverage, redundancy/usefulness, counterexamples, constructor refinement, and refinement-excluded arms independently of parser syntax. Implementation refinement remains a separate obligation.
