# Tagging and Labeling

This canvas describes Oak's **tagging** system:

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

* Tags annotate additional protocol semantics (e.g. "this really is an HTTP header name").

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

* Keep tags on their own logical "column" so they read like annotations, not extra code.
