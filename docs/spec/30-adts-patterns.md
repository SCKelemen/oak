# ADTs and Pattern Matching

This document is normative for Oak algebraic data types and matching.

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

A match over a closed ADT must be exhaustive.

The checker accepts a match when either:

- every constructor is covered; or
- an otherwise valid wildcard/binding catch-all covers the remainder.

A missing constructor is a compile-time error.

For large scalar domains such as `u32` or strings, finite literal arms are not exhaustive without a wildcard/binding remainder.

Redundant/unreachable arms should be diagnosed.

## 8. Constructor narrowing

Inside a constructor arm, the scrutinee is known to be that constructor and payload bindings have the constructor's payload type/refinement.

Conceptually:

```oak
x: Option[T]

x ?
  | .Some(v) => ... // v: T
  | .None    => ...
```

For future GADT-style constructors, matching may additionally introduce constructor-specific propositions/equalities into the arm's proof context.

This should extend ordinary ADT matching rather than create separate GADT match syntax.

## 9. GADT direction

Oak's long-term GADT feature should be understood as **ADTs whose constructors refine type indices/result propositions**.

For example, a length-indexed vector constructor conceptually proves facts about the resulting length index. Exact surface syntax is not yet normative.

The design requirements are:

- constructor-specific refinements enter the branch context;
- impossible branches can reduce to `never`;
- pattern matching is the elimination form;
- runtime representation need not carry proof-only indices when they are erasable;
- proof erasure must preserve executable semantics.

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

Initial formal obligations include:

- constructor coverage/exhaustiveness for finite ADTs;
- match selection is deterministic;
- only the selected branch is evaluated;
- constructor narrowing yields the declared payload type/refinement;
- `never` branches do not widen a match result;
- erased proof/index information does not alter runtime constructor semantics.

The first Lean model should formalize finite constructor sets and exhaustiveness independently of parser syntax. Later refinement work can relate compiler constructor tables/match checking to that model.
