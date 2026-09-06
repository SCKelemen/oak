# Oak Surface Syntax

This document defines the canonical surface conventions. Compatibility spellings in older documents are not normative.

## 1. Punctuation has one job

Oak prefers a tight syntactic surface in which punctuation carries a stable meaning.

| Syntax | Meaning |
| --- | --- |
| `x: T` | type annotation |
| `x = e` | initialization with explicit type context or reassignment |
| `x := e` | local declaration with inferred type |
| `(A, B) -> C` | function type |
| `pattern => expr` | match arm |
| `Type.Case` | qualified ADT constructor |
| `.Case` | context-inferred ADT constructor |
| `T[E]` | generic/type application |
| `[]T` | read-only view |
| `[*]T` | writable span |
| `[N]T` | fixed-size owned array |

`->` is not a match-arm spelling. `=>` is not a function-type spelling.

`Type::Case` is legacy syntax and not canonical.

## 2. Declarations

Explicitly typed declaration:

```oak
count: u32 = 0
```

Inferred local declaration:

```oak
count := u32(0)
```

Reassignment:

```oak
count = count + 1
```

Safe Oak does not assign an implicit `NULL` value to an uninitialized declaration. A declaration such as:

```oak
x: T
```

is not part of the safe core until definite-initialization semantics are specified and mechanically checked. Prefer initialization at declaration or an explicit `Option[T]`/state ADT.

## 3. Functions

Canonical return annotation uses `:`:

```oak
fn add(a: i32, b: i32): i32 = a + b
```

Layout body:

```oak
fn add(a: i32, b: i32): i32
  sum := a + b
  sum
```

Explicit body:

```oak
fn add(a: i32, b: i32): i32 {
  sum := a + b
  sum
}
```

These forms have one block/expression semantics. `=` is useful for an explicitly expression-bodied function; a following layout block or brace block is the ordinary body form.

Function types use `->`:

```oak
(i32, i32) -> i32
```

## 4. Blocks and layout

Statement/expression blocks may be delimited by indentation or explicit braces. Both normalize to the same structural token stream and AST.

```oak
while ready
  work()
  advance()
```

is equivalent to:

```oak
while ready {
  work()
  advance()
}
```

There is no file-wide syntax mode. Explicit braces dominate indentation inside the explicit block.

Data-construction braces remain explicit:

```oak
Point { x: 1, y: 2 }
```

Layout indentation never changes a record literal into a statement block or vice versa.

## 5. Separators

Commas delimit elements inside data/parameter/type argument lists:

```oak
f(a, b, c)
Point { x: 1, y: 2 }
Result[T, E]
```

A trailing comma may be allowed for multiline delimited data/lists when the corresponding grammar production explicitly permits it. The parser uses one delimited-sequence cursor contract regardless of the element kind.

Semicolons may separate statements in explicit single-line blocks, but normal Oak formatting uses line structure and does not require semicolons after ordinary statements.

## 6. ADTs

```oak
Option[T]: type =
  | Some: T
  | None
```

Constructors:

```oak
x: Option[i32] = Option.Some(42)
y: Option[i32] = .None
```

## 7. Pattern matching

```oak
value ?
  | .Some(x) => x
  | .None    => fallback
```

Explicit braces:

```oak
value ? {
  | .Some(x) => x
  | .None    => fallback
}
```

The leading `|` is canonical in multiline form because it visually exposes the closed set of alternatives. Inline formatters may omit redundant whitespace but not change semantics.

## 8. Records

Type:

```oak
Point: type = {
  x: i32
  y: i32
}
```

Value:

```oak
p := Point { x: 1, y: 2 }
```

Anonymous record values/types may be supported where context makes the type unambiguous, but named construction is preferred at boundaries because it preserves nominal intent.

## 9. Generics and constraints

```oak
fn map[A, B](xs: []A, f: (A) -> B): ()
  ...
```

Constraints use `:` and conjunction:

```oak
fn copy[T: Reader & Writer](x: T): ()
  ...
```

`&` in a generic constraint means “satisfies both constraints.” Record composition, if retained, is a separate definition-time operation despite sharing the token.

## 10. Unsafe

Unsafe code is visibly scoped:

```oak
unsafe {
  p.* = value
}
```

or an explicitly unsafe function/operation where the syntax is later finalized. `unsafe` does not disable normal typing; it marks a boundary where additional assumptions are admitted.

## 11. Canonical formatting

`oak fmt` is responsible for choosing canonical whitespace while preserving semantics. It should support at least:

```text
--style=layout
--style=explicit
```

Both styles format the same AST. The formatter should not preserve obsolete punctuation aliases merely because the parser temporarily accepts them for migration.
