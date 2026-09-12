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

## 2a. String literals

A string literal is delimited by double quotes and holds UTF-8 text
(`70-strings.md`). The scanner decodes the following escape sequences, once,
so every later phase — the evaluator, `text_literal`, the C backend's own
re-escaping — sees the bytes the program means:

| Escape | Byte |
| --- | --- |
| `\n` `\t` `\r` | line feed, horizontal tab, carriage return |
| `\0` | NUL |
| `\\` `\"` | backslash, double quote |
| `\xHH` | one byte, exactly two hexadecimal digits |

Any other character after a backslash is an invalid escape and the literal
is a parse error; there is no silent fallback. `\xHH` may produce a byte
that is not valid UTF-8 on its own; the literal as a whole must still be
valid UTF-8 where a `string` is required, and a `[]u8` context accepts any
bytes. There is no raw-string form in v1: a literal that must contain a
backslash spells it `\\`.

Motivation recorded in `docs/notes/ml-feedback-2026-09.md` (finding F1): a
code emitter cannot write a newline into its output without it.

## 2b. Discard statements

`_ = expr` evaluates `expr` and drops its non-unit result on purpose
(`85-discipline.md` §6). `_` is not a variable and binds nothing;
`_: T = expr` and `_ := expr` are not declarations and are rejected as
they are today. The form is a statement, never an expression.

## 2c. List literals take their shape from context

A bare list literal `[e1, e2, ...]` has no type of its own. It takes the
array or view shape its context expects — a declaration's type, a
parameter's type at a call, a function's return type, a record field's
type, or the element type of an enclosing literal — and its elements are
checked against that shape's element type, so `[1, 2, 3]` is a `[3]u32`
where a `[3]u32` is expected, a `[]u32` view where a view is expected, and
`[[1, 2], [3, 4]]` fills a `[2][2]u32`. The literal is then exactly the
typed form `[N]T{ ... }` or `[]T{ ... }` the author could have written, in
every position those are legal:

```oak
sum3: (xs: [3]u32): u32 = xs[0] + xs[1] + xs[2]
dims: (shape: []u32): u32 = len(shape)

xs: [3]u32 = [1, 2, 3]
total: u32 = sum3([4, 5, 6])          // an owned [3]u32 argument
rank: u32 = dims([28, 28])            // a view over two u32
corners: (): [2]Point = [Point { x: 0.0, y: 0.0 }, Point { x: 1.0, y: 2.0 }]
```

Rules:

- An owned-array context `[N]T` requires exactly `N` elements; a different
  count is an error naming both counts. A view context `[]T` (or a span
  `[*]T`) takes the literal's own length.
- Every element is checked with the context's element type as its expected
  type, so integer literals take that width and a float literal in an
  integer context is an error, as anywhere else.
- A literal with no array or view context (`xs = [1, 2]` with `xs`
  undeclared, a literal passed where a scalar is expected) is rejected; the
  compiler does not guess a shape.
- A literal in a view or span context denotes call-local storage: the C
  backend lowers it to a view over a C99 array compound literal, whose
  lifetime is the enclosing block (`90-backend.md` §10), long enough for
  the call or initializer it appears in and no longer. Such a view cannot be
  returned or stored beyond that block — the borrow rules of
  `50-borrowing.md` apply to it as to any view of a local.

The variadic form of §3 is the other spelling of the same thing:
`dims(28, 28)` and `dims([28, 28])` reach a `dims: (shape: ...u32)` or
`dims: (shape: []u32)` callee as the same two-element view.

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

A function type may carry an effect row, `(i32) -> i32 effects { }`
(`60-effects-allocation.md` §2a): a value of the type performs at most the
listed effects, which the effect analysis checks where a value enters the
type and relies on where a call goes through it.

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
  (`cond ? (a | b) | c` — first arm `(a | b)`, second arm `c`). Every
  bracketed construct restores `|` as an operator for its extent —
  parentheses, call arguments, index brackets, array and record
  literals, and brace blocks, however deeply the arm nests them
  (`cond ? f(a | b) | c` calls `f` with `a | b`; a block arm's
  statements read `|` as the operator); everywhere else, bare `|` is
  bitwise or. A Bool conditional has two arms, so a third
  bare `|` after them is a **parse error** that names the fix
  (`cond ? a | b | c` used to parse as `(cond ? a | b) | c`, an or over
  the whole conditional — the F16 misreading; it no longer parses).

## 3c. Function literals

A function literal is a function value written in expression position. Its
typed shape carries the same annotations a declaration does, and it is
checked exactly like one: each parameter has its declared type and the body
must produce the declared result.

```oak
inc := fn(x: u32): u32 = x + 1
add: (u32, u32) -> u32 = fn(a: u32, b: u32): u32 { a + b }
total := apply(fn(x: u32): u32 = x * 2, total)
say := fn(): () = {}
```

Rules:

- The typed shape is recognized by `name :` right after the opening
  parenthesis, or by `()` followed by a return annotation. The return
  annotation uses `:` or `->`, the body is `{ block }` or `= expression`
  (`= {` opens a block, as for declarations). A literal takes no variadic
  parameter.
- The untyped shape `fn(a, b) { ... }` remains for the REPL and legacy
  tests; its parameters default to `i32`. Annotate to get anything else.
- A literal is a code pointer, never an environment: capturing an enclosing
  local is rejected (`OAK-T0401`, `60-effects-allocation.md` §11) unless
  the capture has justified storage. One shape does today: a literal
  passed (directly, or bound to a local used once) to a top-level,
  non-generic function whose function parameter only flows into calls —
  its own, or those of functions it forwards the parameter to — capturing
  scalar, string, view, span, or plain-data record and sum-type parameters
  or annotated locals it does not rebind, is specialized away — the callee
  chain is cloned for the call site and the captured values travel as
  arguments (`60-effects-allocation.md`
  §11, `compiler/closures.go`). A typed literal lowers
  to a plain top-level C function (`90-backend.md` §9); the expression is
  that function's address — no closure object, no allocation, no indirect
  dispatch beyond the pointer the program itself asked for.

Motivation recorded in `docs/notes/roadmap-authority-resources.md` (asks,
tier 2): resource fixtures needed literals whose parameters are handles.

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

### 4a. Line breaks end calls, indexes, and subtractions

A call or an index never continues across a line break: a line that begins
with `(` or `[` begins a new statement (F18). `f(x)` followed by a line
`(a + b) == c ? ...` is two statements, not `f(x)(a + b)`. The same holds
for `-`: a line that begins with a minus negates what follows, it does not
subtract from the line above — `x := 1` followed by a line `-x == 0 - 3 ? ...`
is a negation, not `1 - x`. (`!` has no infix reading and always starts a
statement.) Inside parentheses and brackets nothing changes (they are
continuation contexts), and an operator at the end of a line still
continues the expression: `50 -` followed by a line `8` is one subtraction.
This is Go's rule without the semicolon insertion; `;` remains available to
put two statements on one line. `Oak.StatementBoundary`
(`spec/lean/Oak/StatementBoundary.lean`) models the rule — the decision reads
only the next token's kind and the two lines; a token on the same line never
begins a statement; a boundary kind on a later line always does; other kinds
never do — and checks the three examples above by evaluation.

## 4b. Deferred statements

`defer` schedules a statement to run when the enclosing block ends:

```oak
process: (path: string): u32 {
  h: Handle = open(path)
  defer close(h)
  read(h)
  count(h)
}
```

The rules, all static:

1. `defer` is a keyword and takes one statement — a call, an assignment,
   or a discard (`defer _ = f()`; the discard rule of `85-discipline.md`
   §6 applies to a deferred call as anywhere).
2. The deferred statement runs when the **enclosing block** ends — a brace
   or layout block, a `?` arm, a `while` body, the function body — after
   the block's value has been computed and before the block yields it. In
   a loop body it runs at the end of every iteration. Several `defer`s in
   one block run in reverse order of appearance.
3. `break` runs the pending deferred statements of every block it leaves,
   innermost first, before leaving.
4. The deferred statement is **evaluated when it runs**, not when it is
   written: `defer close(h)` closes whatever `h` names at the block's end.
   Nothing is captured and nothing is allocated.
5. `defer` outside a block is an error.

`defer` is a reordering the compiler performs on the syntax tree before
any analysis: the block above is checked, borrow-checked, executed, and
lowered exactly as if it were written with `close(h)` after the tail
expression has been bound to a temporary. Every later phase therefore
sees the deferred call where it runs, which is why `defer close(h)`
discharges a terminal-state obligation (`50-borrowing.md` §9) and a use of
`h` after the block is a use after consumption. The canonical formatter
keeps `defer` where the programmer wrote it.

## 4c. Bare block statements

A `{ ... }` on its own in statement position is a **block statement**: a
scope of its own, whose bindings end with it, so sibling blocks may reuse a
name and a resource borrowed inside is released at the closing brace
(`50-borrowing.md` §9: suspension and dependency are lexical). Assignments
inside reach the declaring scope.

```oak
x: u32 = 1
{
  y: u32 = 41
  x = x + y
}
{
  y: u32 = 100
  _ = y
}
```

Every brace block is a scope in the same way: function bodies, `while`
bodies, the arms of a `?`, and a `defer` (§4b) runs at the end of the block
that holds it, so a bare block bounds deferred cleanup too. In statement position the brace is a block unless
it reads as record syntax — `{ x: 1, y: 2 }` (a field list reaching `,` or
`}` before any `=`), or `{ r | ... }` (an extensible record type) — which
the REPL evaluates as an expression. The C backend emits the block as a C
compound statement, so the scopes agree.

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


## 12. Pipeline and field-accessor expressions

Oak admits the left-associative pipeline operator `|>`. `value |> f` is equivalent to `f(value)`; `value |> f(a, b)` is equivalent to `f(a, b, value)`. It binds more loosely than Boolean, comparison, and arithmetic operators and more tightly than a match expression, and introduces no allocation.

A leading-dot lowercase identifier is a structurally polymorphic field accessor: `.name(record)` is equivalent to `record.name`, and `record |> .name` selects `record.name`. Leading-dot uppercase identifiers remain inferred ADT constructors (`.Ok`, `.Some(value)`). The accessor requires exactly one argument and works for every record or struct whose type guarantees that field; it captures no environment and causes no record boxing.

An accessor is also a first-class function when a concrete unary function type supplies its layout: `getter: (Person) -> string = .name` and `map(.name, people)` specialize `.name` to the selected struct at that use site. Generic-call inference first learns the record type from the other arguments, then learns the accessor result from that record's field. A bare inferred binding such as `getter := .name` is rejected because it supplies no concrete layout. Native lowering uses a typed static field-projection function and an ordinary function pointer; it introduces no closure environment, dispatch table, allocation, or boxing.

## 13. Uniform call syntax

`recv.f(args)` is a call of `f` with `recv` as its first argument whenever
`recv` is a value (not a package alias) and its type has no method or field
named `f`. It is syntax, not dispatch: the callee is fixed at compile time,
named by `f`, and the form lowers to the plain call `f(recv, args...)` in
every backend and in the interpreter — no vtable, no thunk, no allocation.

```oak
Vec: type = struct { x: f32, y: f32 }
scale: (v: Vec, k: f32): Vec = Vec { x: v.x * k, y: v.y * k }
norm1: (v: Vec): f32 = v.x + v.y

n: f32 = v.scale(2.0).norm1()      // norm1(scale(v, 2.0))
h: u32 = view(&xs).first()         // first[u32](view(&xs)): generics infer as usual
```

Resolution of `recv.f(args)`, in order:

1. If `recv` is an ADT and a method `fn (r: T) f` is declared, the call is
   that method (`83-modules.md` §6.5).
2. If `recv`'s type has a field `f`, the form is an error: fields are read,
   never called through this syntax, so `p.callback(1)` cannot silently
   change meaning when a function named `callback` appears.
3. Otherwise `f` is a function visible at the call site — the enclosing
   package's own, a selective or open import, the prelude — or, when
   `recv`'s type is declared by an imported package, an **exported**
   function `f` of that package, as if written `alias.f(recv, args)`.
   Unexported functions of other packages are not reachable: the `pub`
   boundary is the same as for a qualified call.
4. Nothing found is an error naming `f` and the receiver's type.

The rewritten call is then checked exactly as `f(recv, args...)`: arity,
argument types, generic inference, borrow and effect rules, and the
discipline profile all apply to the plain call, and their diagnostics name
it. Chaining is left-associative because `.` binds tightest (§1):
`x.matmul(w).relu()` is `relu(matmul(x, w))`.

The receiver is the **first** argument. The pipeline operator of §12 puts
its value **last** (`v |> f(a)` is `f(a, v)`); both conventions are stated
so that `x.f(a)` and `x |> f(a)` are never confused — the former matches
method calls, the latter a data-last pipeline.
## 14. Operator definitions

An `operator(SYM)` marker before a function declaration binds the symbol
`SYM` for a left operand of the function's first parameter type:

```oak
Vec: type = struct { x: f32, y: f32 }
operator(+) add: (a: Vec, b: Vec): Vec = Vec { x: a.x + b.x, y: a.y + b.y }
operator(*) scale: (v: Vec, k: f32): Vec = Vec { x: v.x * k, y: v.y * k }
operator(==) same: (a: Vec, b: Vec): Bool = a.x == b.x && a.y == b.y

c: Vec = a + b * 2.0          // add(a, scale(b, 2.0))
```

The function keeps its name: it is called, exported, and found by that
name, and `a + b` is exactly `add(a, b)` — a statically bound call with
the same arity, argument, borrow, effect, and discipline checking as the
spelled-out call, whose diagnostics name `add`. Nothing is dispatched and
nothing is hidden: every `+` on a `Vec` names one function a reader can
find in the package that declares `Vec` (`00-constitution.md`, no hidden
work).

Rules:

- **Symbols.** `+ - * / % == != < <= > >=` may be bound. `&& || ! & | ^ <<
  >>` keep their fixed Bool and bitwise meaning (§3b) and are not
  bindable; there are no unary bindings, no new symbols, no user-defined
  precedence, and no compound assignment. A bound symbol keeps its grammar
  precedence, so `a + b * 2.0` groups as it always did.
- **Left operand type.** The first parameter must be a declared record or
  ADT type. Primitives, strings, arrays, views, and spans keep their
  built-in operators and cannot be rebound. The second parameter may be
  any type: `Vec * f32` is `scale`.
- **Home package.** The declaration must live in the package that declares
  the left operand's type (`83-modules.md` §6.5, the same rule as for
  methods): a call's meaning never depends on which unrelated package is
  compiled. A binding on an imported type is an error.
- **One binding per type and symbol.** A second `operator(+)` for the same
  left type is an error naming the first.
- **Comparisons return Bool.** `== != < <= > >=` bindings must have a
  `Bool` result. Nothing requires them to be consistent with one another;
  `derive.equal` (`40-records.md`) remains the structural equality.
- **Resolution.** In `a SYM b`, if the checked type of `a` is a declared
  type with a binding for `SYM`, the expression is the bound call: `b` is
  checked with the second parameter's type as its expected type (so a
  literal takes it), and the result is the function's return type. A
  declared type without a binding for `SYM` keeps today's error. Operands
  evaluate left to right, as call arguments do.
- **Generics.** v1 bindings are monomorphic: the left operand type is a
  concrete declared type, not a generic instance or type parameter.

Lowering: the checker records the callee of each bound infix expression,
and an elaboration pass after type checking rewrites it into the ordinary
invocation, so the borrow checker, discipline, lowering, both backends,
and the interpreter never see an operator (`compiler/operators.go`). The
declared operator properties of `docs/notes/ml-feedback-2026-09.md` item
7.3 (`associative`, `commutative`, `neutral`) are a later refinement over
these bindings and are not part of this section.

### 14a. Operator laws

An operator definition may declare, on the author's authority, the algebraic
properties its operation has:

```oak
operator(+) add: (a: Vec, b: Vec): Vec laws { associative, commutative } = ...
```

`laws { ... }` follows the effect clauses and names any of `associative`
(`(a + b) + c = a + (b + c)`), `commutative` (`a + b = b + a`),
`identity(e)` (`e + a = a` and `a + e = a`, where `e` is an expression of
the operand type — a nullary function call such as `hist_zero()` or a
named constant), and `idempotent` (`a + a = a`). Every law needs two
parameters of one type; all but `commutative` need the result to be that
type too, and `identity` needs its element to be of that type — an
`identity` without an element, or an element on any other law, is a
diagnostic. `associative` with `identity(e)` is the declaration of a
monoid; adding `commutative` makes it commutative, and `idempotent` a
join-semilattice (`docs/notes/algebraic-semantics-2026-09.md` §3). A law
is a **permission, not an optimization hint**: it is the only
ground a backend or a library has to regroup or reorder applications of the
operator (`55-parallelism.md` section 4). Without a declared law, the
grouping a program names is the grouping computed — floating-point `+`
declares nothing, so `reduce.tree` over floats yields the same bits on every
target.

**The first consumer.** A call of `reduce.tree(xs, zero, f)` whose `f`
names an operator definition declaring `associative` is lowered to
`reduce.chain(xs, zero, f)` — the left fold from the first element, `zero`
only for the empty view, no stack of partials — by
`Oak.Reduce.tree_eq_chainFold`: under associativity the binary-counter
tree and the chain are one value on every input. The lowering is a
rewrite of the call site in the type checker, so the C backend, the
interpreter, and the extraction all compute the chain, and the semantic
model lists every such site (`LawLowerings`: the operator, the call
lowered from and to). `reduce.tree` with any other combine — a plain
function, an operator without the law — is the tree it names, and so is a
kernel's reduction (`56-kernels.md` §7): operators are declared over
records, which are outside the kernel subset.

Laws are declared, not checked by the type checker: like `effects { }` on
an extern, the declaration is the author's claim. The tooling keeps it
visible and discharges what it can. `oak vet` lists declared laws with
their elements. `oak prove` (`125-verification.md` §3) states each law as a
theorem named `law_<function>_<law>` — `law_merge_associative`,
`law_merge_identity_left`, `law_merge_identity_right`,
`law_merge_idempotent` — over the operand type and runs the discharge
ladder: when the operand is a record of `u8`, `u16`, `Bool`, or a
refinement of those small enough for `-cases`, the law is decided
exhaustively or refuted with the counterexample operands; a larger operand
leaves the theorem open for Lean. The REPL's `:lean` states the same
theorems over the extracted definition (`95-extraction.md`), each with the
shape its law fixes (`identity` binds the element through the fuel monad
before the application), so the claim can be proved rather than repeated.
Declaring a false law makes a regrouped result differ
from the named grouping — floating-point addition declared associative
turns `tree` over `[2^24, 1, 1, 1]` from `2^24 + 2` into the chain's
`2^24` (`compiler/e2e_laws_consumer_test.go`); nothing else in the
language depends on it.

