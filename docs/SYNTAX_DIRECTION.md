# Oak Syntax Direction

Oak supports one language with two equivalent surface styles:

- **layout style**: indentation and line structure delimit statement bodies;
- **explicit style**: `{ ... }` and `;` delimit the same bodies.

The parser must normalize both forms to the same AST. Style must never change semantics.

## Principle

```text
source text
    |
    v
scanner (preserves trivia)
    |
    v
layout normalizer
    |
    +-- explicit braces/separators pass through
    +-- indentation produces virtual braces/separators
    |
    v
one parser
    |
    v
one AST
```

There is no global "syntax mode". A source file may mix styles where doing so remains unambiguous.

## Equivalent examples

Layout style:

```oak
fn sum(xs: []u32): u32
  total: u32 = 0
  i: uint = 0
  while i < len(xs)
    total = total + u32(xs[i])
    i = i + 1
  total
```

Explicit style:

```oak
fn sum(xs: []u32): u32 {
  total: u32 = 0;
  i: uint = 0;
  while i < len(xs) {
    total = total + u32(xs[i]);
    i = i + 1;
  }
  total
}
```

Mixed style is valid when structurally clear:

```oak
fn sum(xs: []u32): u32 {
  total: u32 = 0
  i: uint = 0
  while i < len(xs)
    total = total + u32(xs[i])
    i = i + 1
  total
}
```

All three forms must produce the same AST.

## Layout rule

Oak uses an off-side rule only where the grammar expects a statement body.

When a body begins without an explicit `{`:

1. the first body token establishes the body's indentation column;
2. tokens beginning at that column start sibling statements;
3. a greater indentation belongs to the current statement/expression;
4. a smaller indentation closes virtual blocks until the token is valid at the new level;
5. EOF closes all remaining virtual blocks.

The normalizer emits synthetic tokens:

- `VIRTUAL_LBRACE`
- `VIRTUAL_RBRACE`
- `VIRTUAL_SEMI`

The parser treats virtual and explicit delimiters equivalently but preserves their origin for formatting and diagnostics.

## Newlines are not generally semicolons

A newline becomes a virtual separator only when all of these are true:

- the parser/layout context is inside a layout-delimited statement body;
- delimiter nesting (`()`, `[]`, explicit `{}` used as expressions/data) does not require continuation;
- the next token begins at the active layout column;
- the previous token can terminate a statement/expression.

This avoids Python-style accidental sensitivity inside expressions.

```oak
x := foo(
  a,
  b,
)
```

is one expression, not three statements.

## What is layout-delimited

Initial scope:

- function bodies;
- `while` bodies;
- `unsafe` bodies;
- statement blocks used by control-flow constructs;
- block-valued match arms.

Later grammar additions (protocols, proof blocks, effects, state machines) should use the same body abstraction rather than inventing new indentation rules.

## What remains explicitly delimited

For the first implementation, braces that construct data remain explicit:

```oak
Point { x: 1, y: 2 }
{ x: 1, y: 2 }
```

Likewise, brackets and parentheses remain explicit. This prevents layout syntax from making record literals or grouped expressions ambiguous.

Record *type declarations* may gain an indentation form later if the grammar can prove it unambiguous; that is separate from statement-block layout.

## Tabs

Indentation is measured in source columns, not bytes. Tabs in leading indentation are rejected by the layout normalizer. This removes editor-dependent semantics. Tabs may still occur in strings/comments.

## Formatting

`oak fmt` should support at least:

- `--style=layout`
- `--style=explicit`

Because both styles share one AST, formatting between them is mechanical.

## Correctness properties

The layout implementation must test and eventually prove:

1. **style equivalence**: layout and explicit forms normalize to equivalent token structure and identical ASTs;
2. **idempotence**: formatting and reparsing does not change semantics;
3. **explicit dominance**: indentation inside an explicit block never closes that block;
4. **balanced virtual delimiters**: normalization always produces balanced virtual braces;
5. **determinism**: one token/trivia stream has exactly one normalized token stream;
6. **source fidelity**: synthetic tokens carry source positions but never destroy original trivia.

## Design constraint

Layout is syntax sugar, not a second grammar. Any future feature that requires separate semantic rules for layout and explicit syntax is a design failure and should be redesigned.