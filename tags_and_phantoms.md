Here are the two “canvases” as markdown docs. I’ll keep them self-contained so you can drop them into SPEC / docs as-is.

---

# ADT and Pattern Matching

This canvas defines Oak’s algebraic data types (ADTs) and pattern matching syntax, using only the current surface decisions:

* ADTs are declared with `Name: type = ...`
* Variants use `| Case`, `| Case: Payload`, `| Case: Payload = default`, or `| Case := default`
* Pattern matching uses `expr ?` with `| pattern => block` arms
* `->` is reserved for function *types* only
* No `::` syntax; constructors are `Type.Case` (or `.Case` where unambiguous)

---

## 1. Declaring ADTs

### 1.1 Simple variants (no payloads)

```oak
Color: type =
  | Red
  | Green
  | Blue

// Values
c1: Color = Color.Red
c2: Color = Color.Green
c3 := Color.Blue        // type inferred
```

Semantics:

* `Color` is a closed sum type with three cases.
* Each case has implicit `Unit` payload (`{}`), but you typically don’t see it.

---

### 1.2 Variants with payload types

```oak
Option[T]: type =
  | Some: T
  | None

Result[T, E]: type =
  | Ok: T
  | Err: E

maybe: Option[i32] = Option.Some(42)
nothing: Option[i32] = Option.None

res1: Result[i32, string] = Result.Ok(10)
res2: Result[i32, string] = Result.Err("oops")
```

* `Some: T` declares a case with payload type `T`.
* `None` has implicit `Unit` payload.

---

### 1.3 Variants with explicit underlying scalar values

Scalar-ish enums with explicit payload type and value:

```oak
Comparison: type =
  | Less:    i8 = -1
  | Equal:   i8 = 0
  | Greater: i8 = 1

cmp1: Comparison = Comparison.Less
cmp2: Comparison = Comparison.Greater
```

Interpretation:

* All cases share payload type `i8`.
* `= -1`, `= 0`, `= 1` are *payload defaults* for each case.
* From the typechecker’s perspective, this is still just “sum of named payloads”; backend may later special-case this to a compact enum.

---

### 1.4 Variants with inferred payload types

When the payload type can be inferred from the default expression, you can omit the type and use `:=`:

```oak
Comparison2: type =
  | Less   := -1    // payload type inferred as i8
  | Equal  := 0
  | Greater := 1

cmp: Comparison2 = Comparison2.Equal
```

Rules:

* `:= expr` means “payload type inferred from `expr`”.
* All cases in the same ADT must still be type-compatible (e.g., all numeric).

---

### 1.5 Variants with record payloads and defaults

Record payloads are common for “enum with data attached”:

```oak
StatusPayload: type = {
  code: u16
  msg: string
}

Status: type =
  | Ok:           StatusPayload = { code: 200, msg: "Ok" }
  | Unauthorized: StatusPayload = { code: 401, msg: "Unauthorized" }
  | Forbidden:    StatusPayload = { code: 403, msg: "Forbidden" }
  | NotFound:     StatusPayload = { code: 404, msg: "Not Found" }

s1: Status = Status.Ok         // uses default payload {code: 200, msg: "Ok"}
s2: Status = Status.NotFound
```

You can treat `Status` as “a small closed set of defaulted records”:

```oak
fn code(s: Status): u16 =
  // payload type is StatusPayload, so we can access fields
  s.code

fn message(s: Status): string =
  s.msg
```

---

## 2. Constructing ADT values

### 2.1 Qualified constructors

Explicit qualification:

```oak
maybe: Option[i32] = Option.Some(42)
none: Option[i32] = Option.None
cmp: Comparison = Comparison.Less
```

### 2.2 Shorthand `.Case` when the type is known

When the expected type is known, you can elide the type name and use `.Case`:

```oak
maybe: Option[i32] = .Some(42)
none: Option[i32] = .None

status: Status = .NotFound
```

This is purely syntactic sugar; the compiler resolves the type from context.

---

## 3. Pattern matching: syntax

### 3.1 Basic shape

Pattern matching is an expression, written with `?` and `| pattern => block` arms:

```oak
expr ?
  | pattern1 => block1
  | pattern2 => block2
```

Examples use two block styles:

* **Indentation-based**:

  ```oak
  x ?
    | 0 => "zero"
    | 1 => "one"
    | _ => "other"
  ```

* **Braced**:

  ```oak
  x ? {
    | 0 => { "zero" }
    | 1 => { "one" }
    | _ => { "other" }
  }
  ```

Formatter should vertically align `?`, `|`, and `=>`.

---

### 3.2 Matching simple values

```oak
fn describe_int(x: i32): string =
  x ?
    | 0 => "zero"
    | 1 => "one"
    | _ => "other"
```

Patterns allowed here:

* Literals: `0`, `1`
* Wildcard: `_`

---

### 3.3 Matching ADTs without payloads

```oak
StatusSimple: type =
  | Ok
  | Error

fn status_code(s: StatusSimple): i32 =
  s ?
    | StatusSimple.Ok    => 200
    | StatusSimple.Error => 500
```

With shorthand:

```oak
fn status_code2(s: StatusSimple): i32 =
  s ?
    | .Ok    => 200
    | .Error => 500
```

---

### 3.4 Matching ADTs with payloads

#### 3.4.1 Generic `Option`

```oak
fn unwrap_or_zero(x: Option[i32]): i32 =
  x ?
    | Option.Some(value: i32) => value
    | Option.None             => 0
```

With `.Some` shorthand:

```oak
fn unwrap_or_zero2(x: Option[i32]): i32 =
  x ?
    | .Some(value: i32) => value
    | .None             => 0
```

Here:

* `value: i32` is a *typed binding pattern*: “bind this payload as `value` of type `i32`”.
* In generic code, you’d write `value: T`.

#### 3.4.2 Record payloads

Using the earlier `Status`:

```oak
fn is_error(s: Status): Bool =
  s ?
    | Status.Ok(_)           => Bool.False
    | Status.Unauthorized(_) => Bool.True
    | Status.Forbidden(_)    => Bool.True
    | Status.NotFound(_)     => Bool.True
```

Binding the payload:

```oak
fn http_message(s: Status): string =
  s ?
    | Status.Ok(p: StatusPayload)           => p.msg
    | Status.Unauthorized(p: StatusPayload) => p.msg
    | Status.Forbidden(p: StatusPayload)    => p.msg
    | Status.NotFound(p: StatusPayload)     => p.msg
```

(We can add record-field destructuring patterns later; for now, we bind the whole payload.)

---

### 3.5 Matching generic ADTs

Generic over payload type:

```oak
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(x: A) => Option.Some(f(x))
    | Option.None       => Option.None
```

Generic `Result`:

```oak
Result[T, E]: type =
  | Ok: T
  | Err: E

fn bind_result[A, B, E](
  res: Result[A, E],
  f: (A) -> Result[B, E]
): Result[B, E] =
  res ?
    | Result.Ok(x: A)   => f(x)
    | Result.Err(e: E)  => Result.Err(e)
```

---

### 3.6 Type-based patterns

Oak supports *type patterns* that match on runtime type and optionally capture:

```oak
fn describe_type(x: any): string =
  x ?
    | s: string => "string"
    | n: i32    => "i32"
    | _         => "something else"
```

* `s: string` matches values of type `string` and binds them as `s`.
* `n: i32` matches values of type `i32` and binds them as `n`.
* `_` is the catch-all.

You can combine this with ADTs:

```oak
Value: type =
  | Int: i32
  | Text: string

fn describe_value(v: Value): string =
  v ?
    | Value.Int(n: i32)   => "int " + string(n)
    | Value.Text(s: string) => "text " + s
```

---

### 3.7 Variable bindings and wildcards

Patterns can:

* Bind a name: `x: i32`, `p: StatusPayload`
* Ignore a value: `_`
* Combine with constructor patterns: `Option.Some(x: T)`, `Status.Ok(_)`

Some examples:

```oak
fn first_some(a: Option[i32], b: Option[i32]): Option[i32] =
  a ?
    | .Some(x: i32) => .Some(x)
    | .None         => b
```

---

## 4. Blocks in pattern arms

Pattern arms’ right hand side is always a *block expression*.

Single expression (indentation):

```oak
fn parity(n: i32): string =
  (n % 2) ?
    | 0 => "even"
    | _ => "odd"
```

Multi-statement block:

```oak
fn describe_and_log(x: i32): string =
  x ?
    | 0 => {
        log("saw zero")
        "zero"
    }
    | _ => {
        log("saw non-zero")
        "non-zero"
    }
```

Braced form with nested blocks:

```oak
fn describe_status(s: Status): string =
  s ? {
    | .Ok(p: StatusPayload) => {
        log("ok " + string(p.code))
        p.msg
    }
    | _ => {
        "error"
    }
  }
```

Both indentation and brace-based blocks are first-class; the formatter should normalize and align them.

---

---

# Tagging and Labeling

This canvas describes Oak’s **tagging** system:

* Structural tags using `{ key: value }` syntax after ADT arms and record fields.
* Tagging in the presence of generics and phantom types.
* Tags are compile-time metadata only, not runtime fields.

For now:

* Tags are only allowed on **record fields** and **ADT arms**.
* Tags are written as `` `{ … }` `` immediately after the field or arm definition.
* Tag values are anonymous record literals with restricted payload types.

---

## 1. Tag syntax overview

### 1.1 Tags on ADT arms

You can attach a tag to any variant:

```oak
Comparison: type =
  | Less:      i8 = -1 `{ description: "less than",      number: 7     }`
  | Equal:    i8 = 0  `{ description: "equal to",        number: 59   }`
  | Greater: i8 = 1  `{ description: "greater than", number: 100 }`
```

Generic ADT:

```oak
Option[T]: type =
  | Some: T `{ description: "some", number: 20 }`
  | None      `{ description: "none",  number: 30 }`
```

Inference form:

```oak
Comparison2: type =
  | Less      := -1 `{ description: "less than",       number: 100 }`
  | Equal    :=  0  `{ description: "equal to",        number: 100 }`
  | Greater :=  1  `{ description: "greater than", number: 100 }`
```

Shape:

```text
| CaseName [: PayloadType] [= default | := default] ` { tagFields } `
```

---

### 1.2 Tags on record fields

Record fields can also be tagged:

```oak
FieldInfo: type = {
  a: u32 `{ i32: 12, string: "a" }`
  b: u32 `{ i32: 34, string: "b" }`
}
```

With default values:

```oak
WithDefaults: type = {
  a: u32 = 0      `{ i32: 12, string: "a" }`
  b: u32 = 255 `{ i32: 34, string: "b" }`
}
```

Formatter guideline: tags for fields in the same record should be vertically aligned.

---

## 2. Tag value grammar and constraints

Tag values are **anonymous record literals** with a restricted set of leaf types:

* Keys: identifiers (`description`, `code`, `i32`, `string`, etc.)
* Leaf values:

  * String literals: `"Ok"`, `"Not Found"`, `"my_field"`
  * Numeric literals: `123`, `-1`, `3.14` (whatever numeric forms Oak supports)
* Composite values:

  * Record literals:

    ```oak
    `{ meta: { id: 123, name: "example" } }`
    ```
  * Array literals:

    ```oak
    `{ bytes: []u8{ 1, 2, 3 } }`
    ```

### 2.1 Nested record tags

```oak
Example1: type =
  | Recursive `{ a: { b: { id: 123 } } }`
  | Equal        `{ a: { b: { id: 456 } } }`
```

Here, both variants carry metadata under the same nested shape.

### 2.2 Tags with arrays

```oak
Example2: type =
  | Recursive `{ a: []u8{ 1, 2, 3 } }`
  | Equal
```

* `Recursive` has a tag with a single field `a` that is a `[]u8` array literal.
* `Equal` has no tag.

---

## 3. Use cases for tags on ADTs

Tags provide structured, compile-time metadata about variants, separate from their payload types.

### 3.1 Enums with human-readable labels and codes

```oak
StatusPayload: type = {
  code: u16
  msg: string
}

Status: type =
  | Ok:           StatusPayload = { code: 200, msg: "Ok" }
      `{ name: "ok", category: "success" }`
  | Unauthorized: StatusPayload = { code: 401, msg: "Unauthorized" }
      `{ name: "unauthorized", category: "client_error" }`
  | Forbidden:    StatusPayload = { code: 403, msg: "Forbidden" }
      `{ name: "forbidden", category: "client_error" }`
  | NotFound:     StatusPayload = { code: 404, msg: "Not Found" }
      `{ name: "not_found", category: "client_error" }`
```

This lets you:

* Keep **semantic** fields in the payload (`code`, `msg`).
* Attach **extra metadata** for reflection / UI / docs without polluting the runtime type:

  * e.g. canonical `name`, `category`, grouping information, docstrings.

### 3.2 Protocol codes and wire formats

```oak
WireMessageKind: type =
  | Handshake: u8 = 1  `{ doc: "initial handshake",     phase: "startup"    }`
  | Data:            u8 = 2 `{ doc: "application payload", phase: "active"      }`
  | Close:          u8 = 3 `{ doc: "connection close",     phase: "teardown" }`
```

Backend and tools can use tags to:

* Generate protocol documentation.
* Drive codegen for C enums / message tables.
* Provide reverse lookup tables for debugging.

---

## 4. Use cases for tags on records

Tags on record fields carry metadata like:

* DB column names / constraints
* Serialization info (JSON / Protobuf / CBOR)
* UI labels, units, or display hints

Example:

```oak
User: type = {
  id: u64
    `{ db_column: "user_id", primary_key: 1 }`

  email: string
    `{ db_column: "email", unique: 1 }`

  age: u32 = 0
    `{ db_column: "age", nullable: 1, unit: "years" }`
}
```

These tags can drive:

* Migration / schema tools
* Serialization frameworks
* UI form generators

Again: tags are metadata; they do not automatically change runtime layout.

---

## 5. Tagging + generics + phantom types

Tags and phantom types solve *different* problems but compose nicely:

* **Phantom types** encode semantic distinctions in the type system (no runtime footprint).
* **Tags** attach structured metadata to fields/variants (compile-time constants, potentially reflected at build time).

### 5.1 Phantom IDs with tags

```oak
Id[T]: type = u64

UserTag: type = {}
OrderTag: type = {}

User: type = {
  id: Id[UserTag]
    `{ db_column: "user_id", domain: "user" }`

  email: string
    `{ db_column: "user_email" }`
}

Order: type = {
  id: Id[OrderTag]
    `{ db_column: "order_id", domain: "order" }`
}
```

* `Id[UserTag]` vs `Id[OrderTag]` are type-distinct (phantom).
* Tags annotate DB metadata, domains, etc.

### 5.2 Encodings and text types

```oak
Utf8: type = {}
Ascii: type = {}

Encoded[Tag]: type = {
  bytes: []u8
}

Header: type = {
  name: Encoded[Ascii]
    `{ http_header: 1 }`

  value: Encoded[Utf8]
    `{ http_header_value: 1 }`
}
```

* Phantom `Tag` encodes the logical encoding at the type level.
* Tags annotate additional protocol semantics (e.g. “this really is an HTTP header name”).

---

## 6. Consuming tags (conceptual)

The *language* just defines the syntax and static constraints. How you read tags is a library / tooling concern (e.g. `std.reflect`, compiler plugins, code generators).

Conceptual example (not a committed API):

```oak
// Pseudo-API to get the tag for a variant
fn status_tag(s: Status): Tag =
  reflect.variant_tag(s)

// Pseudo-API to get record-field tags
fn field_tags[T](field: Field[T]): Tag =
  reflect.field_tag(field)
```

Tools could use this to:

* Build reverse lookup tables:

  ```oak
  fn try_to_status(code: u16): Option[Status] =
    // hypothetical reflection-based implementation
    std.status.from_code(code)
  ```

* Generate documentation or API clients based solely on tags & types.

For now, you only need the **syntax and constraints** nailed down to start annotating enums and records; reflection can come later.

---

## 7. Formatting guidelines

To keep tagged structures readable, the formatter should:

* Align tags across variants in the same ADT:

  ```oak
  Comparison: type =
    | Less:    i8 = -1 `{ description: "less than",  number: 7 }`
    | Equal:   i8 = 0  `{ description: "equal to",   number: 59 }`
    | Greater: i8 = 1  `{ description: "greater than", number: 100 }`
  ```

* Align tags across fields in the same record:

  ```oak
  WithDefaults: type = {
    a: u32 = 0   `{ i32: 12, string: "a" }`
    b: u32 = 255 `{ i32: 34, string: "b" }`
  }
  ```

* Keep tags on their own logical “column” so they read like annotations, not extra code.

