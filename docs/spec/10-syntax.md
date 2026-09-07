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

A function is an ordinary declaration: a name bound to a function interface
and a definition, exactly like every other `name: Type = value` form.

```oak
addi32: (a, b: i32): i32 = a + b
addu8: (a, b: u8) -> u8 = a + b
```

Both return spellings are accepted: `:` and `->`. Parameter names may be
grouped, sharing one type (`a, b: i32`); the last group may be variadic
(`rest: ...T`, one name). The definition is `= expression`, `= { block }`,
or a brace block:

```oak
mix: (a: u8, b, c: i32) -> i32 {
  b + c
}

add(l: u32, r: u32): u32 = {
  l + r
}
```

The second shape is the **colon-less form**: the name is followed directly
by its parameter list. It is recognized when the parentheses carry a
parameter annotation (`name: type` at top level of the list) or when an
empty list is followed by a return annotation; otherwise `name(...)` is a
call. After `=`, a `{` opens a block body — a whole-body record literal
must use its named form (`= Point { ... }`), which is preferred at
boundaries anyway (§8).

The `fn` keyword form remains available (methods with receivers and generic
type parameters currently use it) with the same body semantics:

```oak
fn add(a: i32, b: i32): i32 = a + b
```

Function types (interfaces without a definition) use `->` and appear anywhere
a type does — a variable of function type holds a function value:

```oak
handler: (i32, i32) -> i32 = addi32
```

### Variadic trailing parameters

The last parameter may be variadic, Go-style:

```oak
fn total(base: i32, rest: ...i32) -> i32
```

Inside the body, `rest` is `[]i32` — a read-only view. A call supplies at
least the fixed arity; the trailing arguments (possibly none) are
materialized into a **caller-owned stack array** whose view lives exactly as
long as the call: the cost is explicit at the call site and nothing is
heap-allocated (`Oak.Variadic` proves bundling neither drops nor duplicates
arguments and the view length equals the trailing count). Spreading an
existing sequence (`f(xs...)`) is not yet specified. Only the final
parameter may carry the marker; `..` is not a token.

## 3a. Conditionals are matches

Oak has **no `if`/`else` keywords**. The one branching form is the match
expression `?`, and a Boolean condition is just a match over `Bool`. Sugar
makes the two-arm case read naturally — all of these are the same match:

```oak
condition ? branch1 | branch2

condition ?
          | branch1
          | branch2

condition ?
          | true  => branch1
          | false => branch2
```

Branches are expressions or brace blocks; block branches may contain
statements, so conditional mutation is ordinary:

```oak
v[i] < best ? {
  best = v[i]
  bestIndex = i
}
```

Conditionals are **expressions**: with both branches present, the match
produces a value, block branches yielding their trailing expression.

```oak
sign: (n: i32): i32 = n < 0 ? { 0 - 1 } | { 1 }

s: i32 = ready ? {
  bonus: i32 = 3
  bonus + 1
} | 0
```

Omitting the second branch supplies an implicit empty (unit) branch, so a
one-armed condition is legal in statement position (a one-armed
*expression* branch requires the block form: `cond ? { x }`); in value
position both branches are required, which the type checker enforces
(unit never equals the value type). Positional branches are recognized by
the absence of `=>`/`->` in the first arm; pattern arms behave exactly as
in §7.

**Lowering** is the compiler's job, not the syntax's: statement-position
conditions emit plain C `if`/`else`; value positions with expression
branches emit a single-evaluation ternary; value positions with
statement-bearing block branches hoist to a declaration plus branch
assignment — in every case the C a careful author would have written by
hand, with the condition evaluated exactly once.

`&&` and `||` are short-circuit connectives over `Bool` (the right operand
evaluates only when the left leaves the result open); `!` is negation.
They bind looser than comparison: `a == b || c < d` reads as
`(a == b) || (c < d)`.

**Design guidance — Boolean blindness.** `Bool` is the type of *answers to
comparisons at a use site*, not a modeling tool. A domain state deserves an
ADT whose constructors name the states (and carry their evidence), matched
with `?` — `Line: type = | Idle | Pending: Cause | Masked` beats three
Booleans that can drift into impossible combinations, and a match on it
cannot forget which case it is in. Reach for the Bool sugar when the
condition is genuinely a comparison (`i < n`, `x == limit`); reach for an
ADT when the condition *is the domain*.

### 3a.1 The evidence rule

The single-arm statement form (`v > best ? { best = v }`) is the FLOOR:
a Bool consumed at the moment it is produced, with nothing bound. It is
honest sugar over the two-arm Bool match, and fine for a raw guard — but
a Bool that crosses any distance is boolean blindness. The
doctrine-conformant spellings, in ascending order:

```oak
Ordering: type = Less | Equal | Greater

cmp[T]: (a: T, b: T): Ordering {
  a < b ? .Less | (a == b ? .Equal | .Greater)
}

// evidence-carrying: the match binds WHY, exhaustively
cmp(v, best) ?
  | .Greater => { best = v }
  | .Less => { }
  | .Equal => { }

// domain function: the conditional mutation disappears entirely
best = max(best, v)
```

`cmp` and `max` are written once, generically (`20-types.md` §11.2), and
the Bool sugar bottoms out the tower — some primitive comparison must
exist, and everything above it is constructed evidence.

## 3b. Bitwise and shift operators

The register-bitfield vocabulary: `&` (and), `|` (or), `^` (xor), `<<`,
`>>`, and prefix `^` (complement — Go's spelling; there is no `~`).
Integer literals admit `0xFF` and `0b1010` sugar beside the canonical
radix form (`16rFF`, `2r1010`).

```oak
hcr: u64 = hcrVM | hcrFMO | (u64(1) << 27)
cleared: u64 = hcr & ^hcrFMO
field: u64 = (hcr >> 3) & 0x3
```

Rules:

- **Unsigned-only, same-width.** Both operands are the same unsigned
  fixed-width type; literals infer through the operator (the left
  operand types the right, so `hcr & 0x19` and `v << 3` need no
  annotations). No signed bitwise, no C promotion rules: bitwise on a
  signed value is a modeling smell — convert explicitly
  (`u32_bits_i32`).
- **Precedence is Go's**: `<< >> &` bind at the multiplicative level,
  `| ^` at the additive level. `x & mask == 0` parses as
  `(x & mask) == 0`, not C's famous trap.
- **Shifts are never UB.** A constant count is statically checked
  against the operand width (`x << 32` on `u32` is a compile error); a
  variable count that reaches the width traps at runtime (`oak_shl_u32`
  and friends — the bounds-check doctrine; constant counts fold the
  check away under optimization).
- **The arm rule.** Inside a bare-expression `?`-match arm body, `|` is
  the arm separator; parenthesize to use bitwise or there
  (`cond ? (a | b) | c` — first arm `(a | b)`, second arm `c`). Brace
  blocks and parentheses restore `|` as an operator; everywhere else,
  bare `|` is bitwise or.

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

Inline declarations take no leading pipe — the `=` already introduces the
alternatives, and payload-carrying variants are unambiguous (aliases are
bare identifiers, records use braces):

```oak
Case: type = Upper | Lower | Title | Modifier | Other
Shape: type = Circle: i32 | Square: i32 | Empty
```

In multiline layout the leading pipe is canonical, exposing the closed set
of alternatives down the margin:

```oak
Option[T]: type =
  | Some: T
  | None
```

An indexed constructor writes its explicit result after `=>`:

```oak
Expr[T]: type =
  | Int: i64  => Expr[i64]
  | Flag: Bool => Expr[Bool]
  | Id: T     => Expr[T]
```

The result must be the enclosing ADT applied to exactly its declared type
indices. Omitting the result is equivalent to returning the enclosing ADT with
its parameters unchanged. This `=>` is declaration punctuation; match arms
use the same token in expression context.

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

## 8. Records and structs

Oak deliberately separates **semantic record shape** from **runtime struct representation**.

A record type describes named product semantics without promising a byte layout:

```oak
XY: type = {
  x: f32
  y: f32
}
```

Such a type may participate in compile-time reasoning, constraints, schemas, proofs, and tooling even when no concrete runtime representation is required.

A struct type selects concrete ordered storage representation as part of the declaration:

```oak
Point: type = struct {
  x: f32
  y: f32
}
```

`struct` is therefore a representation-bearing type form, not a synonym for `{ ... }`.

The default `struct` policy is the natural ordered representation specified in `40-records.md`: declaration order is layout-significant, fields receive aligned non-overlapping storage, and final size is tail-padded to record alignment. Future packed/extern/explicit-offset policies must be selected explicitly rather than changing plain record semantics.

Named value construction remains:

```oak
p := Point { x: 1, y: 2 }
```

The value-construction braces do not themselves select a representation; the value's type does.

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

A semantic record type may also be used as a structural shape requirement in a constraint position once shape constraints are implemented:

```oak
XY: type = { x: f32, y: f32 }

fn length2[T: XY](value: T): f32
  value.x * value.x + value.y * value.y
```

This means `T` must expose the required semantic fields. It does **not** require `T` to share the same runtime layout as `XY`, and it does not create a runtime interface object or vtable. Shape-constraint implementation remains separate from ordinary value subtyping.

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
