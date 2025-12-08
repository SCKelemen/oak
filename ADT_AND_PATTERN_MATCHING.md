# ADT and Pattern Matching

This canvas defines Oak's algebraic data types (ADTs) and pattern matching syntax, using only the current surface decisions:

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

* Each case has implicit `Unit` payload (`{}`), but you typically don't see it.

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

* From the typechecker's perspective, this is still just "sum of named payloads"; backend may later special-case this to a compact enum.

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

* `:= expr` means "payload type inferred from `expr`".

* All cases in the same ADT must still be type-compatible (e.g., all numeric).

---

### 1.5 Variants with record payloads and defaults

Record payloads are common for "enum with data attached":

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

You can treat `Status` as "a small closed set of defaulted records":

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

* `value: i32` is a *typed binding pattern*: "bind this payload as `value` of type `i32`".

* In generic code, you'd write `value: T`.

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

Pattern arms' right hand side is always a *block expression*.

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
