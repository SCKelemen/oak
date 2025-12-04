# Oak Language Specification (Draft)

> **Status:** Exploratory design, focused on MCU-friendly, C-like compilation with strong static guarantees.

---

## 1. Design Goals

* Compile to **simple C** that a competent firmware engineer could have written by hand.
* Target **microcontrollers** (e.g. STM32, RP2350) with tight resource constraints.
* Fixed-width integers, **no hidden allocations**, no GC, no exceptions.
* Prefer **value-oriented** APIs, explicit ownership, and clear borrowing.
* Keep the language small, **expression-oriented**, and amenable to **Go-like compile times**.
* Separate:
  * **Type layer** (APIs, ADTs, interfaces, semantics)
  * **Layout layer** (in-memory and on-wire representation).

---

## 2. Core Types

### 2.1 Primitive integers

* Signed: `i8`, `i16`, `i32`, `i64`
* Unsigned: `u8`, `u16`, `u32`, `u64`

**Overflow semantics:**

* All integer arithmetic wraps modulo 2^N (two's complement) for bit width N.
* No UB from integer overflow in safe code.

**Division:**

* `a / b` for integers:
  * Division by zero is an error (exact behavior TBD: trap vs unsafe-only).
  * Signed division rounds **toward zero**.

### 2.2 Derived core types

```lang
Bool: type
  = False
  | True

Byte: type = u8
Rune: type = i32

Option[T]: type
  = None
  | Some(T)

Result[T, E]: type
  = Ok(T)
  | Err(E)

Comparison: type
  = Less
  | Equal
  | Greater
```

* `Bool` is a 2-case ADT.
* `Byte` is an alias, mainly for clarity.
* `Rune` matches Go's choice (`i32`) for Unicode scalar values.
* `Option` and `Result` are canonical ADTs for optionality and error handling.
* `Comparison` is used for explicit ordering APIs.

### 2.3 Unit type

* `()` represents "no meaningful value".
* Functions that don't return data use `-> ()`.

### 2.4 String type

* `string` is a read-only slice of bytes: `string == []u8`
* String literals are compile-time constants.
* No separate string type with hidden allocation.

---

## 3. Modules, Packages, and Imports

### 3.1 Package declaration

Each source file starts with exactly one `package` declaration:

```lang
package main
```

or:

```lang
package http
package checked
package myapp
```

All files sharing a package name within a build unit belong to the same package namespace.

### 3.2 Imports (function-style)

Imports are **top-level** and use function-style syntax:

```lang
import(http)            // sugar: binds as `http`

http := import(http)    // explicit binding name
json := import(json)

renamed: module = import(net)
```

Rules:

* `import(pkg)` at top level is sugar for `pkg := import(pkg)`.
* `name := import(pkg)` binds the imported package/module to `name`.
* Optional type annotation `: module` is allowed but not required.
* Imported names are used as `name.Symbol` or `name.Type::Variant`.

### 3.3 Visibility

Visibility is **Go-style, by capitalization**:

* Identifiers starting with an uppercase letter are **exported** from their package.
* Identifiers starting with a lowercase letter are **package-private**.

This applies to:

* types (`Status` vs `statusImpl`)
* functions (`NewClient` vs `newClient`)
* methods (`Code` vs `codeImpl`)
* ADTs and variants (`Status`, `Ok`, `NotFound`)

### 3.4 Entrypoint

Program entry:

```lang
package main

fn main() -> i32
  ... // last expression is the exit code
```

* There must be exactly one `main` function in `package main`.

---

## 4. Types, Aliases, ADTs

### 4.1 Type alias

```lang
Byte: type = u8

StatusRaw: type =
  { code:   u16
  , status: string
  }
```

* `Name: type = T` defines `Name` as a type alias or ADT, depending on the right side.

### 4.2 Records / structs

Records are product types with named fields:

```lang
Config: type =
  { enabled: Bool
  , threshold: u8
  }
```

Alternate formatting styles (all equivalent):

```lang
Config: type = { enabled: Bool, threshold: u8 }

Config: type
  = { enabled: Bool
    , threshold: u8
    }
```

Layout:

* Record layout is implementation-defined but stable within a given target ABI.
* Type layer does **not** guarantee layout; layout-related APIs (e.g. for wire formats) are explicit.

### 4.3 ADTs / Union types

Sum types with tagged variants:

```lang
Status: type
  = Ok
  | NotFound
  | Unauthorized
  | Forbidden

Option[T]: type
  = None
  | Some(T)

RxState: type
  = WaitingForHeader
  | WaitingForLen
  | WaitingForPayload(Span[Byte])
  | Done(u16)
```

* Variants can be:
  * bare constructors (`Ok`), or
  * single-parameter constructors (`Some(T)`), written `.Some(x)`.
* Multi-field payloads are to be added later.

### 4.4 Variant literal tags

A union (ADT) variant may have a **single literal value** associated with it using `:`:

```lang
Status: type
  = Ok:           200
  | NotFound:     404
  | Unauthorized: 401
  | Forbidden:    403
```

```lang
Status: type
  = Ok:           "Okay"
  | NotFound:     "Not Found"
  | Unauthorized: "Unauthorized"
  | Forbidden:    "Forbidden"
```

```lang
Status: type
  = Ok:           { code: 200, status: "Okay" }
  | NotFound:     { code: 404, status: "Not Found" }
  | Unauthorized: { code: 401, status: "Unauthorized" }
  | Forbidden:    { code: 403, status: "Forbidden" }
```

#### Rules

* Each variant may have **exactly one** literal after `:`.
* All variants in a given type must have literals of the **same type**. That common type is the **raw type** of the ADT.
* Allowed literal kinds:
  * Primitive integer literals: `u8, u16, u32, u64, i8, i16, i32, i64`
  * String literals
  * Record literals whose fields are themselves literals of the above kinds, recursively.
* These literals are **compile-time constants**.
* They **do not change the runtime representation** of the union.

#### Runtime Representation

The ADT itself remains a **small tagged union** at runtime. `Status` values like `.Ok` / `.NotFound` are just **small tags** (e.g. `u8` / enum), not pointers. The literal metadata is used by the compiler to generate accessors and can be implemented as inline constants or a static lookup table.

Runtime C-ish representation:

```c
typedef enum {
    STATUS_Ok,
    STATUS_NotFound,
    STATUS_Unauthorized,
    STATUS_Forbidden,
} Status;
```

#### Raw Type and `raw()` Accessor

For an ADT with literal record values, the compiler infers a **raw type**:

```lang
StatusRaw: type =
  { code:   u16
  , status: string
  }
```

Conceptually, the compiler can synthesize:

```lang
fn (s: Status) raw() -> StatusRaw
  s ?
    | .Ok           -> { code: 200, status: "Okay" }
    | .NotFound     -> { code: 404, status: "Not Found" }
    | .Unauthorized -> { code: 401, status: "Unauthorized" }
    | .Forbidden    -> { code: 403, status: "Forbidden" }
```

For numeric or string raw values, `raw()` returns that primitive type:

```lang
Status: type
  = Ok:           200
  | NotFound:     404
  | Unauthorized: 401
  | Forbidden:    403

fn (s: Status) raw() -> u16
  s ?
    | .Ok           -> 200
    | .NotFound     -> 404
    | .Unauthorized -> 401
    | .Forbidden    -> 403
```

Implementation strategies for `raw()` in C/IR:

1. **Switch-based**: inline constants in a `switch` on the tag.
2. **Table-based**: a static `const` table in `.rodata` indexed by the tag.

Both are zero-runtime-overhead patterns for MCUs.

#### Field Lifting (`s.code`, `s.status`)

If the raw type is a **record**, then for any field `f` of the raw type, the language allows **field lifting**:

```lang
st: Status = .NotFound

code:   u16    = st.code     // sugar for st.raw().code
text:   string = st.status   // sugar for st.raw().status
```

* This is **read-only**; attempting to assign `st.code = 201` is a compile-time error.
* Under the hood, `st.code` lowers to either a `switch` or `table` lookup.

Example C implementation using a table:

```c
typedef struct {
    uint16_t code;
    const char *status;
} StatusRaw;

static const StatusRaw STATUS_RAW_TABLE[] = {
    { 200, "Okay" },
    { 404, "Not Found" },
    { 401, "Unauthorized" },
    { 403, "Forbidden" },
};

StatusRaw Status_raw(Status s) {
    return STATUS_RAW_TABLE[s];
}

uint16_t Status_code(Status s) {
    return STATUS_RAW_TABLE[s].code;
}

const char *Status_status(Status s) {
    return STATUS_RAW_TABLE[s].status;
}
```

On the MCU, `Status` values remain tiny (just the tag), and the metadata is a single readonly table in flash.

#### Simple Numeric / String Raw Values

For simpler ADTs that only attach a single primitive literal:

```lang
Status: type
  = Ok:           200
  | NotFound:     404
  | Unauthorized: 401
  | Forbidden:    403

fn (s: Status) code() -> u16
  s.raw()
```

Similar for string literals:

```lang
Status: type
  = Ok:           "Okay"
  | NotFound:     "Not Found"
  | Unauthorized: "Unauthorized"
  | Forbidden:    "Forbidden"

fn (s: Status) text() -> string
  s.raw()
```

#### Inverse Mappings (Code/Text → ADT)

Inverse mappings (e.g. from integer code or string back to the ADT) are expressed as scalar pattern matches:

```lang
fn to_status(code: u16) -> Option[Status]
  code ?
    | 200 -> .Some(.Ok)
    | 404 -> .Some(.NotFound)
    | 401 -> .Some(.Unauthorized)
    | 403 -> .Some(.Forbidden)
    | _   -> .None
```

```lang
fn to_status_from_string(text: string) -> Option[Status]
  text ?
    | "Okay"        -> .Some(.Ok)
    | "Not Found"   -> .Some(.NotFound)
    | "Unauthorized" -> .Some(.Unauthorized)
    | "Forbidden"   -> .Some(.Forbidden)
    | _              -> .None
```

These lower to straightforward `switch`/`if` chains on integers or string comparisons.

#### Summary

* ADT variants can carry a **single compile-time literal value** (primitive, string, or literal record).
* This literal defines a **raw view** of the ADT but does **not** change the core runtime representation (still a small tagged union).
* The compiler can synthesize `raw()` and support field lifting (`s.code`, `s.status`) when the raw type is a record.
* Implementation on MCUs is zero-cost: tags are small values, and metadata is either inline constants or a static readonly table in flash.
* Inverse mappings from codes/strings back to the ADT are written using the normal scalar `?` pattern matching.

### 4.5 Namespacing variants

* `Type::Variant` refers to a variant of an ADT.
* `pkg.Type::Variant` for fully-qualified names.
* Short form `.Variant` is allowed when the expected ADT type is known from context (e.g. in pattern matching on a `Status`).

---

## 5. Expressions, Pattern Matching, and `?`

### 5.1 Expression-oriented

* The language is **expression-based**: function bodies, match branches, etc. are expressions.
* There is no separate `if` statement in v1; branching uses pattern matching with `?`.

### 5.2 Pattern matching syntax

Preferred, canonical style:

```lang
scrutinee ?
  | pattern1 -> expr1
  | pattern2 -> expr2
  | ...
```

Inline form:

```lang
scrutinee ? | pattern1 -> expr1 | pattern2 -> expr2 | _ -> exprN
```

Braced match block:

```lang
scrutinee ? {
  pattern1 -> expr1
  | pattern2 -> expr2
  | _        -> exprN
}
```

or inline:

```lang
scrutinee ? { pattern1 -> expr1 | pattern2 -> expr2 | _ -> exprN }
```

Arm bodies can themselves be block expressions:

```lang
scrutinee ?
  | pattern1 -> {
      stmt1
      stmt2
      final_expr
    }
  | pattern2 -> other_expr
```

### 5.3 Patterns

Supported pattern forms:

* Wildcard: `_` — matches anything, no binding.
* Binding: `x` — matches anything, binds value to `x`.
* Literal:
  * integer literals: `0`, `200`, `404`
  * string literals: `"GET"`, `"["`
* ADT variants:
  * `.Ok`, `.NotFound`
  * `.Some(x)` (single payload)

Examples:

```lang
code ?
  | 200 -> Status::Ok
  | 404 -> Status::NotFound
  | _   -> Status::InternalServerError

opt ?
  | .Some(v) -> v
  | .None    -> 0

status ?
  | .Ok       -> 0
  | .NotFound -> 1
  | _         -> 2
```

### 5.4 Semantics of `?`

For:

```lang
E ?
  | P1 -> E1
  | P2 -> E2
  | ...
```

* Evaluate scrutinee `E` exactly once.
* Test patterns `P1, P2, ...` in order.
* First pattern that matches is selected.
* Evaluate that branch expression `Ei`; its value is the value of the whole `?` expression.
* Other branches are not evaluated.

**Type rule:**

* All branch expressions `Ei` must have the same type (modulo literal inference).
* That is the type of the `?` expression.

### 5.5 Exhaustiveness

* For ADTs with a finite set of variants:
  * A match on that type must be **exhaustive** or have a wildcard `_` branch.
  * Missing variants cause a compile-time error.

Example:

```lang
Status: type
  = Ok
  | NotFound
  | Unauthorized

status ?
  | .Ok       -> 0
  | .NotFound -> 1
  // ❌ missing Unauthorized, no `_` -> compile error
```

* For scalar types with large/continuous domains (`u16`, `i32`, `string`):
  * Literal patterns match only the given value.
  * A wildcard `_` is required to be exhaustive.

```lang
code ?
  | 200 -> .Ok
  | 404 -> .NotFound
  | _   -> .Unknown   // valid
```

* Any patterns after `_` are unreachable and an error.

### 5.6 Bool as ADT (if-like usage)

Since `Bool` is:

```lang
Bool: type
  = False
  | True
```

An `if` can be written as:

```lang
cond ?
  | .True  -> expr_if
  | .False -> expr_else
```

or:

```lang
cond ?
  | .True -> expr_if
  | _     -> expr_else
```

---

## 6. Functions, Methods, and Calls

### 6.1 Function declarations

Named function:

```lang
fn name(arg1: T1, arg2: T2) -> Ret
  body_expr

fn name(arg1: T1, arg2: T2) -> Ret {
  body_expr
}
```

* Parameters: `name: Type`, comma-separated.
* Return type: `-> Ret` is required; use `()` for no value.
* Body is a **single expression** (possibly a block, `?` match, etc.).
* The value of the body expression is the function's return value.
* There is no `return` keyword in v1; early returns are expressed structurally via expressions.

### 6.2 Methods (Go-style receivers)

```lang
fn (recv: Type) method(arg: ArgType) -> Ret
  body_expr
```

Example:

```lang
Token: type
  = LBRACK
  | RBRACK
  | LCHEV
  | RCHEV

fn (t: Token) lexeme() -> string
  t ?
    | .LBRACK -> "["
    | .RBRACK -> "]"
    | .LCHEV  -> "<"
    | .RCHEV  -> ">"
```

Call syntax:

```lang
t.lexeme()
```

Conceptually desugars to a plain function taking `t` as first argument.

### 6.3 Evaluation order

**Global rule:**

* Expressions evaluate **strictly left-to-right**.
* The compiler must not reorder evaluation of sub-expressions.

For a function call:

```lang
f(arg1, arg2, arg3)
```

* Evaluate `f`.
* Evaluate `arg1`, then `arg2`, then `arg3`.
* Invoke function.

For a method call:

```lang
recv.method(a, b)
```

* Evaluate `recv`.
* Evaluate `a`, then `b`.
* Invoke the underlying method.

### 6.4 Infix operators and precedence

Operators are **left-associative** and have a **single precedence** level unless parentheses are used:

```lang
a + b * c - d
```

is parsed as:

```lang
(((a + b) * c) - d)
```

To get usual arithmetic grouping, parentheses must be explicit:

```lang
a + (b * c) - d
```

No reordering or algebraic simplification is performed by the language semantics (optimizations may perform equivalent transformations if they preserve the exact evaluation order and side effects).

### 6.5 Varargs (Go-style)

Declaring a vararg parameter (must be last):

```lang
fn log(level: Level, msg: string, args: ...string) -> ()
  // inside: args : []string
```

* `args: ...T` is sugar for `args: []T` within the function body.
* Call sites:

```lang
log(.Info, "hello")                          // args = []string{}
log(.Info, "value: {} {}", "a", "b")       // args = ["a","b"]

values: []string = ...
log(.Info, "values: {}", values...)          // args = values
```

* `f(x, y, z)` with varargs constructs a slice for `args`.
* `f(slice...)` passes an existing slice as varargs without copying when possible.

### 6.6 Function types and anonymous functions

Function types:

```lang
Comparator: type = fn(a: i32, b: i32) -> Bool
```

Passing functions:

```lang
fn square(x: i32) -> i32
  x * x

fn apply_twice(f: fn(i32) -> i32, x: i32) -> i32
  f(f(x))
```

Anonymous functions (lambdas):

```lang
fn (x: i32) -> i32
  x + 1

fn use_lambda() -> i32
  apply_twice(fn (x: i32) -> i32
                x + 1,
              10)
```

Closures:

* Lambdas can capture variables from lexical scope.
* Captures are by **value** (copied at closure creation).
* Shared mutable state is explicit via pointers/spans.

Example:

```lang
fn counter(start: i32) -> fn() -> i32
  current: i32 = start
  p: *i32 = &current

  fn () -> i32
    unsafe
      *p = *p + 1
      *p
```

### 6.7 Recursion

* Functions may call themselves recursively.
* By default, recursion is compiled as normal calls (stack growth per call).
* A future `@tailrec` annotation may require the compiler to optimize tail recursion into loops or fail compilation.

---

## 7. Ownership, Slices, and Spans

### 7.1 Goals

* Compile to **simple C** that a firmware/C engineer could have written by hand.
* Avoid Rust-level complexity (no explicit lifetimes in type signatures, no traits soup, no macros).
* Enforce a basic safety rule on borrowed memory:
  * **Many readers OR one writer** for a given region.
* Keep compile times in the **Go ballpark**:
  * Simple syntax, simple type system, no compile-time execution beyond constants.

### 7.2 Core Sequence Types

#### Arrays: `[N]T`

```lang
buf: [256]u8
rows: [8][16]u8
```

* Own storage.
* Length `N` is part of the type.
* Layout = `N * sizeof(T)` contiguous bytes.
* Stack, static, or inside other structs.
* Maps directly to C:

```c
uint8_t buf[256];
uint8_t rows[8][16];
```

#### Read-only slices: `[]T` (views)

Conceptually:

```lang
View[T]: type =
  { base: &T
  , len:  u32
  }

[]T  ==  View[T]
```

* Non-owning window into an existing buffer.
* Read-only: you can only read elements.
* Used for function parameters, substrings, packet views, etc.
* C shape:

```c
typedef struct {
    const T *base;
    uint32_t len;
} View_T;
```

#### Mutable slices: `[*]T` (spans)

Conceptually:

```lang
Span[T]: type =
  { base: &T
  , len:  u32
  }

[*]T  ==  Span[T]
```

* Non-owning window into an existing buffer.
* Read/write: you can mutate through it.
* Used for passing writable windows into buffers, decoding into caller memory, etc.
* C shape:

```c
typedef struct {
    T *base;
    uint32_t len;
} Span_T;
```

#### Relationship

* `[N]T` – owns; fixed length at type level.
* `[]T` / `[*]T` – borrow; each value has a fixed `len` once created, but length is not part of the type.
* There is **no** growable owning sequence type in the core design yet.

### 7.3 Borrowing & Aliasing Rule

We want a simple, Rust-like *semantic* rule without Rust's syntactic complexity:

> For any given memory region, at a time you may have:
>
> * **Any number of** read-only borrows (`[]T`), OR
> * **Exactly one** mutable borrow (`[*]T`),
>
> but not both at once, and not multiple overlapping mutable borrows.

Interpretation:

* `[]T` is a **shared immutable borrow**.
* `[*]T` is a **unique mutable borrow**.

This is enforced by the compiler's static analysis, not by runtime code or smart pointers.

### 7.4 How the compiler enforces this (conceptually)

The compiler tracks, within a function/body:

* Which arrays/buffers exist (owning roots).
* Which slices/spans are derived from which roots.
* For spans, what subrange (offset + length) they cover, when it can be inferred.

Rules:

* It is always safe to form multiple `[]T` views from the same root.
* Forming a `[*]T` span requires that:
  * no overlapping `[*]T` spans from the same root are live, and
  * no overlapping `[]T` views from the same root are live.

In simple cases, this is checked lexically within a function:

```lang
buf: [256]u8 = zero_init()

// ok: read-only
ro: []u8 = buf[0:128]

// error: mutable overlap with live read-only view
rw: [*]u8 = buf[64:192]
```

The compiler does **not** emit any runtime tracking machinery; it just rejects unsafe code.

### 7.5 Escape hatches

When the analysis is too conservative or when interfacing with raw C pointers, the language can provide:

* An `unsafe { ... }` block to bypass aliasing checks.
* Raw pointer types (`&T`, `&mut T`) that behave more like C pointers and are not subject to slice/span alias rules.

These are explicit and localized, so most code stays in the safe, slice/span world.

### 7.6 Bounds Safety

Arrays and slices must be indexed safely.

#### Compile-time bounds checks

* For arrays `[N]T` with constant indices, out-of-range access is a **compile-time error**.

```lang
a: [4]u8
x = a[2]  // ok
x = a[4]  // compile-time error: index out of bounds
```

* For common patterns like looping from `0` to `len`, the compiler must prove safety and can elide runtime checks:

```lang
fn sum(xs: []u16) -> u32
  total: u32 = 0
  i: u32 = 0
  while i < xs.len
    total = total + u32(xs[i])  // proven safe
    i = i + 1
  total
```

#### Safe accessors

For cases where the compiler cannot prove safety statically, the language favors safe APIs over traps:

```lang
fn (xs: []T) get(i: u32) -> Option[T]
fn (xs: []T) try_slice(start: u32, end: u32) -> Option[[]T]
```

* `xs[i]` is allowed only when the compiler can prove it is in range.
* Otherwise, the programmer uses `get` / `try_slice` (explicit `Option`), or `unsafe` if they are certain.

This avoids hidden runtime traps, which are undesirable on MCUs.

### 7.7 Mapping to C (No Smart Pointers)

The "many readers OR one writer" rule is **purely static**.

* Slices and spans lower to plain C structs: `T*` + `len`.
* Arrays lower to plain C arrays.
* There are **no smart pointers** in the generated C.

Example lowering:

```lang
fn fill(buf: [*]u8, v: u8) -> ()
  i: u32 = 0
  while i < buf.len
    buf[i] = v
    i = i + 1
```

C-ish:

```c
typedef struct {
    uint8_t *base;
    uint32_t len;
} Span_u8;

void fill(Span_u8 buf, uint8_t v) {
    uint32_t i = 0;
    while (i < buf.len) {
        buf.base[i] = v;
        i++;
    }
}
```

All aliasing guarantees have already been checked by the compiler before this C is emitted.

### 7.8 Complexity & Compile Times

To stay near Go's compile times:

* No macros or preprocessor.
* No general compile-time execution beyond constant folding.
* No explicit lifetimes in type signatures.
* Simple, monomorphized generics (e.g. `Option[T]`, `View[T]`, `Span[T]`).
* Pattern matching is lowered early to `switch`/`if`.
* The main job of the compiler is:
  * Parse → type-check → basic borrow/alias analysis → lower to C-like IR → emit C.

The borrow model is deliberately restricted so it can be implemented with **local, predictable analysis**, rather than a Rust-like global lifetime system.

### 7.9 Pointer types and operations

Pointer type:

```lang
*T      // pointer to T
```

Operations:

* Address-of: `&expr` → `*T`
* Dereference: `*ptr` (prefix)

**Safe code:**

* Allowed:
  * Take addresses of locals/globals: `p := &x`
  * Compare pointers for equality/inequality: `p == q`, `p != q`
  * Pass pointers around and into FFI.
* Forbidden:
  * Dereference `*p`
  * Pointer arithmetic: `p + 1`, `p - q`
  * Casting integers ↔ pointers
  * Constructing slices directly from raw pointers

These operations are only allowed inside `unsafe` blocks.

---

## 8. Equality and Comparison

### 8.1 Value vs reference equality

The language distinguishes **value equality** and **reference equality**, but exposes both via a small, fixed set of operators and library functions.

#### Value equality

Value equality answers: *do these values represent the same abstract value?*

Operator `==` / `!=` is defined as **value equality** for:

* Primitive integers: `i8/i16/i32/i64`, `u8/u16/u32/u64`
* `Bool`, `Byte`, `Rune`
* `string`

Examples:

```lang
flag_is_true: Bool = (flag == .True)
is_zero:     Bool = (x == 0)
same_str:    Bool = (a == b)      // string content equality
```

For aggregates (records, ADTs, slices), value equality is provided via library helpers, e.g.:

```lang
core.bytes.equal(xs: []Byte, ys: []Byte) -> Bool
```

Direct `==` on unsupported types is a compile-time error.

#### Reference equality

Reference equality answers: *do these references/pointers/slices refer to the same underlying storage (and length)?*

Operator `==` / `!=` is defined as **reference equality** for:

* Pointers: `*T`
  * `p == q` compares raw addresses.
* Slices and spans: `[]T`, `[*]T`
  * `xs == ys` is true iff `xs.base == ys.base` and `xs.len == ys.len`.

Content equality for slices is always explicit via library functions.

### 8.2 Ordering and `Comparison`

Explicit ordering uses the `Comparison` ADT:

```lang
Comparison: type
  = Less
  | Equal
  | Greater
```

Standard library functions:

```lang
fn cmp_i32(a: i32, b: i32) -> Comparison
fn cmp_u32(a: u32, b: u32) -> Comparison
fn cmp_string(a: string, b: string) -> Comparison
```

Use with `?` matching:

```lang
cmp_i32(x, y) ?
  | .Less    -> ...
  | .Equal   -> ...
  | .Greater -> ...
```

Relational operators (`<`, `<=`, `>`, `>=`) are defined only on primitive integers (and possibly `Rune`), and are specified in terms of the same underlying comparison semantics.

---

## 9. Interfaces and Intersection Types

### 9.1 Intersection types

Intersection types express that a type must satisfy **all** of a set of interfaces:

```lang
ReadWriteCloser: type = Reader & Writer & Closer
```

* `A & B` means "a type that implements both `A` and `B`".
* Intersections live in the **type/interface layer** only; they do not imply any particular data layout.
* Typical use is in type aliases and generic constraints.

### 9.2 Interfaces

Interfaces describe required methods using structural typing. Syntax:

```lang
Reader: type =
  interface
    fn (self) read(buf: [*]Byte) -> Result[u32, Error]

Writer: type =
  interface
    fn (self) write(buf: []Byte) -> Result[u32, Error]

Closer: type =
  interface
    fn (self) close() -> Result[(), Error]
```

Rules:

* `interface` contains one or more method prototypes with receiver `self`.
* A concrete type `T` **implements** an interface `I` if it has methods whose receivers and signatures structurally match those in `I`.
* No explicit `implements` declaration is required.

Example implementation:

```lang
Uart: type =
  { regs: *UartRegs }

fn (u: Uart) read(buf: [*]Byte) -> Result[u32, Error]
  ...

fn (u: Uart) write(buf: []Byte) -> Result[u32, Error]
  ...

fn (u: Uart) close() -> Result[(), Error]
  ...
```

Here, `Uart` satisfies `Reader`, `Writer`, and `Closer` structurally.

### 9.3 Interfaces as generic constraints

Interfaces and intersections are used as **constraints** on type parameters in generic functions.

Generic function syntax (minimal form):

```lang
fn copy[T: Reader, U: Writer](dst: U, src: T, buf: [*]Byte) -> Result[u64, Error]
  ...
```

Or with intersections:

```lang
fn serve[T: Reader & Writer & Closer](conn: T, scratch: [*]Byte) -> Result[(), Error]
  ...
```

* `T: Reader` means "type parameter `T` must implement `Reader`".
* `T: Reader & Writer` means "`T` must implement both `Reader` and `Writer`".

Compilation model:

* The compiler **monomorphizes** generic functions for each concrete type instantiation it encounters, emitting direct calls to the concrete methods (no dynamic dispatch).

### 9.4 Reader / Writer / Closer combinations

Canonical IO interfaces:

```lang
Reader: type =
  interface
    fn (self) read(buf: [*]Byte) -> Result[u32, Error]

Writer: type =
  interface
    fn (self) write(buf: []Byte) -> Result[u32, Error]

Closer: type =
  interface
    fn (self) close() -> Result[(), Error]

ReadWriter: type = Reader & Writer

ReadWriteCloser: type = Reader & Writer & Closer
```

These are pure type/interface constructs; there is no mandatory runtime representation or dynamic "interface value" type in v1.

---

## 10. Error Handling

### 8.1 Result Type

The `Result[T, E]` type is the primary error handling mechanism:

```lang
Result[T, E]: type
  = Ok(T)
  | Err(E)
```

### 8.2 Error Propagation

Error propagation uses the `?` operator (postfix):

```lang
fn parse_u16(s: string) -> Result[u16, ParseError]
  // ... parsing logic

fn parse_pair(s: string) -> Result[(u16, u16), ParseError]
  first: u16 = parse_u16(s)?  // propagates Err, unwraps Ok
  second: u16 = parse_u16(s)?  // propagates Err, unwraps Ok
  (first, second)
```

The `?` operator desugars to:

```lang
match result {
  | .Ok(v) -> v
  | .Err(e) -> return .Err(e)
}
```

### 8.3 Explicit Error Handling

For cases where you want to handle errors explicitly:

```lang
result ?
  | .Ok(value) -> {
      // use value
      value
    }
  | .Err(error) -> {
      // handle error
      default_value
    }
```

---

## 11. Unsafe Blocks

### 9.1 Syntax

```lang
unsafe {
  // unsafe operations here
  *ptr = value
  ptr2 = ptr + offset
}
```

### 9.2 Allowed Operations

Inside `unsafe` blocks:

* Dereference raw pointers: `*ptr`
* Pointer arithmetic: `ptr + offset`, `ptr - offset`
* Integer ↔ pointer casts
* Direct slice construction from raw pointers
* Bypass borrow checker checks

### 9.3 Safety Contract

* The programmer is responsible for ensuring memory safety within `unsafe` blocks.
* The compiler assumes all operations are safe and does not emit additional checks.
* Unsafe blocks should be kept small and well-documented.

---

## 12. Compile-Time Evaluation

### 10.1 Constant Folding

The compiler performs constant folding for:

* Arithmetic operations on compile-time constants
* Comparisons on compile-time constants
* Pattern matching on compile-time constants

### 10.2 Variant Tags

Variant tags (section 4.4) are compile-time constants that can be accessed at compile time:

```lang
StatusInfo: type
  = Ok: { code: 200, status: "Okay" }
  | NotFound: { code: 404, status: "Not Found" }

// Compile-time access
const OK_CODE: u16 = StatusInfo::Ok.code  // 200
```

### 10.3 Limitations

* No general compile-time execution of arbitrary code.
* No macros or code generation at compile time.
* Constant expressions must be evaluable without side effects.

---

## 13. Control Flow

### 11.1 While Loops

```lang
while condition {
  // body
}
```

* Condition must be of type `Bool`.
* Body is a block expression.
* No `break` or `continue` in v1 (use pattern matching and early returns).

### 11.2 For Loops (Future)

For loops over slices/arrays may be added in a future version:

```lang
for x in xs {
  // body
}
```

---

## 14. Type System

### 12.1 Type Inference

* Local variables can use type inference: `x := value`
* Function parameters and return types must be explicit.
* Type annotations are optional for locals: `x: i32 = 10` or `x := 10`

### 12.2 Generics

Generic types use square brackets:

```lang
Option[T]: type
  = None
  | Some(T)

Result[T, E]: type
  = Ok(T)
  | Err(E)
```

* Generics are monomorphized at compile time.
* No trait bounds or constraints in v1.

### 12.3 Type Coercion

* Widening conversions are implicit: `u8` → `u16` → `u32` → `u64`
* Narrowing conversions are explicit: `u32(x)` to convert `x: u64` to `u32`
* No implicit conversions between signed and unsigned.

---

## 15. Standard Library (Planned)

### 13.1 Core Types

* `Option[T]`, `Result[T, E]`, `Bool`, `Comparison`
* Primitive integers: `i8` through `i64`, `u8` through `u64`

### 13.2 Slice Operations

* `get(i: u32) -> Option[T]`
* `try_slice(start: u32, end: u32) -> Option[[]T]`
* `len() -> u32`

### 13.3 Built-in Functions

* `zero_init()` - zero-initialize a value
* `sizeof(T) -> u32` - size of type in bytes

---

## 16. Implementation Status

### Completed

* [ ] Scanner/Lexer
* [ ] Parser
* [ ] AST
* [ ] Basic evaluator
* [ ] Type system
* [ ] Pattern matching
* [ ] Borrow checker

### In Progress

* Specification documentation

### Planned

* C code generation
* Standard library
* Package system
* Import resolution

---

## 17. Status and Future Work

This draft specification is **incomplete**. Notable areas to be specified or refined:

* Loops (`while`, `for`), `break`/`continue`, and their expression semantics.
* String representation, `StringView`, and C interop (`CStr`).
* Detailed standard library layout (`core`, `io`, `bytes`, `string`, `checked`, etc.).
* Error handling patterns on MCUs (panic behavior, fatal errors vs `Result`).
* FFI surface (`extern "C" fn`, calling conventions, mapping to C types).
* Tail recursion annotations (e.g. `@tailrec`) and required optimizations.
* More precise layout rules for ADTs and variant literal tags.

The intent is to keep the language:

* small and regular,
* aggressively friendly to static analysis and MCU constraints,
* and always compilable down to clear, auditable C/ELF.

