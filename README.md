# Oak

> **Status**: the only authoritative feature/verification matrix is
> [`docs/spec/STATUS.md`](docs/spec/STATUS.md), and the normative language
> specification lives in [`docs/spec/`](docs/spec/). Examples below may
> describe design direction ahead of the implemented subset; when this
> document and `docs/spec/` disagree, `docs/spec/` wins.

Oak is a systems programming language designed for embedded systems, firmware, and low-level programming. It combines strong type safety, memory safety through borrow checking, and expressive type system features while compiling to simple, readable C code.

## Table of Contents

1. [Overview](#overview)
2. [Syntax](#syntax)
3. [Type System](#type-system)
4. [Memory Management](#memory-management)
5. [Advanced Features](#advanced-features)
6. [Compiler and Tooling](#compiler-and-tooling)
7. [Examples](#examples)

---

## Overview

Oak is designed with these principles:

- **Memory Safety**: Borrow checker prevents data races and memory errors
- **Type Safety**: Strong static typing with algebraic data types and generics
- **Zero-Cost Abstractions**: Compiles to simple C with no hidden runtime
- **Embedded-Friendly**: No garbage collection, predictable memory layout
- **Readable Output**: Generated C code is clean and auditable

### Key Features

- **Algebraic Data Types (ADTs)**: Sum types with pattern matching
- **Borrow Checking**: Rust-like memory safety without lifetimes
- **Views and Spans**: Read-only and writable slices with ownership tracking
- **Phantom Types**: Type-level distinctions with zero runtime cost
- **Struct Tags**: Compile-time metadata on ADT variants and record fields
- **String Encodings**: First-class encoding support (UTF-8, UTF-16, UTF-32, ASCII)
- **Intrusive Data Structures**: Zero-allocation linked lists and queues
- **Generics**: Parametric polymorphism with interface constraints
- **Interfaces**: Go-style implicit interface satisfaction

---

## Syntax

### Packages and Imports

Normative rules: [`docs/spec/83-modules.md`](docs/spec/83-modules.md). A
package is a directory; a module is an `oak.mod` tree; visibility is explicit.

```oak
package main

// Import and bind under the last path segment
import("example.com/hello/geometry")

// Import under an explicit alias
geo := import("example.com/hello/geometry")

// Import sealed to a signature: only Key, key and hash are visible, and
// h.Key is a fresh abstract type (share it with `Key: type = fnv.Key`)
h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")

// Import named members unqualified
{ twice, Box } := import("example.com/hello/util")

// Instantiate a generic package (`package pair[T, N: u32]`)
bytes := import("example.com/hello/pair")[u8, 3]

// Standard library packages (json loads strings, unicode and the core prelude)
import("json")

// Legacy flat prelude: every library name unqualified
import(std)
```

```oak
package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }   // name exported, fields private
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
abs: (v: i32): i32 = v < 0 ? 0 - v | v                // private to the package
```

`open import("...")` binds every exported member unqualified (collisions are
errors, never precedence), and `module name { ... }` declares a nested package
inside a file with its own `pub` boundary.

The `oak` command has the shape of the Go tool (`docs/spec/115-tooling.md`):
`oak build` produces an executable (`-emit-c` for C), `oak run`, `oak install`
into `$OAKBIN`, `oak vet` reports what the checker recorded without generating
code, `oak list [-json] [-deps]` lists packages and imports, `oak test`, `oak
env`, `oak version`, `oak clean -modcache`, `oak doc`, `oak fmt`, `oak completion`,
package patterns (`oak build ./...`), `oak run dir -- args`, and `oak mod
init|download|tidy|edit|graph|why|vendor|verify` alongside the semver commands
below. Build a package with `oak build [dir]`, run it with `oak run [dir]`, fetch
pinned dependencies with `oak mod download`; see `examples/modules`. Versions
are enforced Elm-style at module granularity: `oak mod api` snapshots a
module's public API, `oak mod bump previous.json` requires the `version` in
`oak.mod` to be the exact bump the API diff implies, `oak mod compat
dep-api.json` checks a module's sealed imports against a dependency snapshot,
`oak mod download` refuses an archive whose carried `api.json` its source
does not honor, `oak mod pack` builds that archive and prints its `require`
line, `oak mod upgrade` picks the highest candidate snapshot a module's sealed
imports accept, and `oak mod try` builds against a local candidate to decide
the unsealed ones, and `oak mod tidy -w` reconciles `require` lines with what
the packages import (`docs/spec/82-package-semver.md`). Derived operations are ordinary
declarations whose body the compiler synthesizes from the type:

```oak
point_eq: (a: Point, b: Point): Bool = derive.equal
point_hash: (v: Point): u64 = derive.hash
point_cmp: (a: Point, b: Point): Ordering = derive.compare
point_format: (v: Point, dst: [*]u8): Result[u32, TextError] = derive.format
```

The REPL is module-aware: it compiles every input through the same pipeline,
resolves imports through the working directory's `oak.mod`, and `:obligations`
lists the recorded assumptions the checker could not discharge. `:lean
obligations.lean` states those assumptions as Lean theorems over the models in
`spec/lean` (loop termination over `Oak.Loops`, tail cycles over
`Oak.Discipline`, region disjointness over `Oak.Regions`) for you to prove
there, and `:lean check` runs the repository's Lean toolchain on them from
inside the session; see `spec/lean/Oak/SessionObligationsProved.lean` for the
discharged example.

### Comments

```oak
// Line comment

/* Block comment */

/* Multi-line
   block comment */
```

### Variables

```oak
// With type annotation and initial value
x: i32 = 5

// Type annotation only (uninitialized)
y: i32

// Type inference
z := 10

// Explicit type annotation
name: string = "Oak"
```

### Primitive Types

```oak
// Fixed-width signed integers
i8, i16, i32, i64

// Fixed-width unsigned integers
u8, u16, u32, u64

// Platform-sized types (adapt to target architecture)
int, uint, ptr, uptr

// Floating point (if supported)
f32, f64

// Pointers
*T  // pointer to T (non-numeric, own primitive type)

// Aliases
byte: type = u8
rune: type = i32
```

### Platform-Sized Integer Types

Oak has four platform-dependent sized types that adapt to the target architecture:

- `int` - signed, "native word" integer (for general arithmetic)
- `uint` - unsigned, "native word" integer (for general arithmetic)
- `ptr` - signed integer large enough to hold a pointer (for pointer math)
- `uptr` - unsigned integer large enough to hold a pointer (for pointer math)

**Width on different targets:**

- **32-bit systems** (STM32, etc.):
  - `int == i32`
  - `uint == u32`
  - `ptr == i32`
  - `uptr == u32`

- **64-bit systems**:
  - `int == i64`
  - `uint == u64`
  - `ptr == i64`
  - `uptr == u64`

**Usage guidelines:**

- **For struct fields, message formats, FFI boundaries** → use fixed-width types (`u16`, `i32`, etc.)
- **For locals, temporaries, loop indices, counters** → `int` / `uint` / `ptr` / `uptr` are fine

**Literal inference:**

Integer literals take their type from context: a declared or assigned type, a
parameter or return type, an array index, or the typed operand next to them in
an arithmetic, comparison, or bitwise expression. Only a literal with no
context defaults to `int`:

```oak
a := 5          // a: int (i32 on 32-bit, i64 on 64-bit)
b: uint = 6     // b: uint (u32 on 32-bit, u64 on 64-bit)
d: u32 = 6      // d: u32 (explicit fixed-width)
e: u32 = d + 1  // 1 is u32: same type and wrap rule as d + u32(1)
f: Bool = 2 * d < 4096
n: u8 = d8 + 300  // error: literal 300 does not fit in type u8
```

A literal that does not fit the type its context requires is an error at the
literal; it never silently widens to `int`. Literals span the full `u64`
range: `0xFFFFFFFFFFFFFFFF` and `14695981039346656037` are `u64` constants.

### Pointers

Pointers in Oak are a distinct primitive type `*T` (pointer to T). Pointers themselves are not signed or unsigned - they're just addresses. When you need to treat an address as a number, you use `ptr`/`uptr` conversions.

**Address-of and dereference:**

```oak
x: int = 42
px: *int = &x

arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }
parr: *[4]u8 = &arr

// Dereference (in unsafe block)
unsafe {
  y: int = *px
  *px = 10
}
```

**Pointer ↔ integer conversions:**

All pointer-integer conversions are explicitly **unsafe** and use `ptr`/`uptr`:

```oak
unsafe {
  p: *u8 = &buffer[0]
  
  // Pointer → integer
  addr: uptr = uptr(p)
  
  // Integer → pointer
  q: *u8 = *u8(addr)
  
  // Pointer arithmetic via uptr
  r: *u8 = *u8(addr + 4)
  
  // Pointer difference as ptr (signed offset)
  p2: *u8 = &buffer[16]
  diff: ptr = ptr(p2) - ptr(p)  // signed byte offset
}
```

**Rules:**

- `uptr(T)` and `ptr(T)` casts are only allowed in `unsafe` blocks
- `ptr` is the signed version; `uptr` is the unsigned version
- In safe code, you never do pointer arithmetic directly; you use arrays/views/spans

**Comparisons:**

In safe code:
- Allowed: `p == q`, `p != q` for `*T`
- Disallowed (unless `unsafe`): `<`, `>`, `<=`, `>=` on pointers, arithmetic on pointers

### Numeric Literals

```oak
// Decimal with underscores
count: u32 = 2_000_000
large: i64 = 922_337_203_685_477_5807

// Radix-based literals (base 2-16)
bin: int = 2r1010        // Binary: 10
oct: int = 8r777         // Octal: 511
hex: int = 16rFFFF       // Hexadecimal: 65535
addr: uptr = uptr(16r1000)  // 4096 in decimal

// Underscores in radix literals
large_hex: int = 16rFF_FF_FF_FF
```

### Functions

```oak
// Expression-bodied function
fn add(a: i32, b: i32): i32 = a + b

// Block function
fn multiply(a: i32, b: i32): i32 {
  a * b
}

// Method syntax (Go-style)
fn (self: Point) distance(): f64 {
  // Calculate distance
}

// Generic function
fn identity[T](value: T): T = value

// Generic with constraints
fn process[T: Readable](item: T): () {
  // Process item
}
```

### Algebraic Data Types (ADTs)

```oak
// Simple variant list
Color: type = Red | Green | Blue

// Shorthand syntax
Color := Red | Green | Blue

// With payloads
Option[T]: type =
  | Some: T
  | None

// With default values
Comparison: type =
  | Less: i8 = -1
  | Equal: i8 = 0
  | Greater: i8 = 1

// With inferred payload types
Comparison2: type =
  | Less := -1
  | Equal := 0
  | Greater := 1

// Record type (single variant ADT)
Point: type = {
  x: i32
  y: i32
}
```

### Pattern Matching

```oak
// Basic pattern matching
result: Option[i32] = Option.Some(42)

value: i32 = result ?
  | Option.Some(x: i32) => x
  | Option.None => 0

// Multiple syntaxes for pattern arms
value ?
  | Option.Some(x: i32) => x
  | Option.Some(x: i32) -> x  // -> and => are equivalent
  | Option.None => 0

// Type patterns
value ?
  | _: string => "string"
  | _: i32 => "i32"
  | _ => "anything else"

// Wildcard patterns
value ?
  | Option.Some(_) => "some"
  | _ => "none"

// Block form
result ?
  | Option.Some(x: i32) => {
      log("got value: " + string(x))
      x
    }
  | Option.None => 0
```

### Records

```oak
// Record type definition
Point: type = {
  x: i32
  y: i32
}

// Record literal
p: Point = { x: 10, y: 20 }

// Multiline record literal
p2: Point = {
  x: 10
  y: 20
}

// With trailing commas
p3: Point = {
  x: 10,
  y: 20,
}

// Record composition (at definition time)
Point2: type = { x: i32, y: i32 }
Point3: type = Point2 & { z: i32 }

// Field access
x: i32 = p.x
```

### Arrays, Views, and Spans

```oak
// Fixed-size array
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// View (read-only slice)
view: []u8 = arr[:]        // Full view
view2: []u8 = arr[1:3]     // Partial view
view3: []u8 = arr[2:]      // From index 2 to end
view4: []u8 = arr[:3]      // From start to index 3

// Span (writable slice)
span: [*]u8 = span(&arr)

// Built-in functions
v: []u8 = view(&arr)
s: [*]u8 = span(&arr)
mid: []u8 = subslice(v, 1, 2)
```

**Using platform types with arrays/views/spans:**

```oak
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }
v: []u8 = view(&arr)

// Use uint for loop indices and counters
fn sum_view(xs: []u8): uint = {
  acc: uint = 0
  i: uint = 0
  while i < len(xs) {
    acc = acc + uint(xs[i])   // explicit widening if needed
    i = i + 1
  }
  acc
}

// Low-level pointer operations (in unsafe)
fn c_memcpy(dst: *u8, src: *u8, n: uptr): () = unsafe {
  i: uptr = 0
  while i < n {
    *(*u8(uptr(dst) + i)) = *(*u8(uptr(src) + i))
    i = i + 1
  }
}
```

### Unsafe Blocks

Oak provides `unsafe` blocks for low-level operations that bypass the borrow checker:

```oak
unsafe {
  // Pointer dereference
  x: int = 42
  px: *int = &x
  y: int = *px
  *px = 10
  
  // Pointer-integer conversions
  p: *u8 = &buffer[0]
  addr: uptr = uptr(p)
  q: *u8 = *u8(addr)
  
  // Pointer arithmetic
  r: *u8 = *u8(addr + 4)
  
  // Pointer comparisons
  p2: *u8 = &buffer[16]
  if p < p2 {
    // Pointer ordering (if supported)
  }
}
```

**Rules:**
- All pointer-integer conversions must be in `unsafe` blocks
- Pointer arithmetic must be in `unsafe` blocks
- Pointer ordering comparisons (if supported) must be in `unsafe` blocks
- In safe code, use arrays/views/spans instead of raw pointer manipulation

### Generics

```oak
// Generic type
Option[T]: type =
  | Some: T
  | None

// Generic function
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) => Option.Some(f(value))
    | Option.None => Option.None

// Generic with multiple type parameters
fn zip[A, B](a: []A, b: []B): []{ first: A, second: B } {
  // Implementation
}

// Generic with constraints
fn process[T: Readable & Writable](item: T): () {
  // Process item
}
```

### Interfaces

```oak
// Interface definition
Readable: interface = {
  Read: ([]u8) -> ReadResult
}

Writable: interface = {
  Write: ([]u8) -> WriteResult
}

// Go-style method binding
fn (self: File) Read(buf: []u8): ReadResult {
  // Implementation
}

// Interface composition
ReadWrite: interface = Readable & Writable

// Generic function with interface constraint
fn copy[R: Readable, W: Writable](reader: R, writer: W): () {
  // Copy from reader to writer
}
```

### Control Flow

```oak
// While loop
i: i32 = 0
while i < 10 {
  i = i + 1
}

// Pattern matching as control flow
result ?
  | Option.Some(x: i32) => {
      // Handle Some
    }
  | Option.None => {
      // Handle None
    }
```

### Struct Tags

```oak
// Tags on ADT variants
Comparison: type =
  | Less: i8 = -1 `{ description: "less than", number: 7 }`
  | Equal: i8 = 0 `{ description: "equal to", number: 59 }`
  | Greater: i8 = 1 `{ description: "greater than", number: 100 }`

// Tags on record fields
User: type = {
  id: u64 `{ db_column: "user_id", primary_key: 1 }`
  email: string `{ db_column: "email", unique: 1 }`
  age: u32 = 0 `{ db_column: "age", nullable: 1, unit: "years" }`
}

// Tag values are compile-time metadata
// - String literals: "value"
// - Numeric literals: 123, -1, 3.14
// - Record literals: { key: value }
// - Array literals: []u8{ 1, 2, 3 }
```

---

## Type System

### Primitive Types

Oak includes fixed-width integers, platform-sized types, pointers, and floating-point numbers:

```oak
// Fixed-width integers
i8, i16, i32, i64
u8, u16, u32, u64

// Platform-sized types (32-bit or 64-bit depending on target)
int, uint, ptr, uptr

// Pointers
*T  // pointer to T

// Floating point
f32, f64

// String type
string: type = Str[utf8]  // UTF-8 encoded string
```

**Platform-sized types:**
- `int` / `uint`: Native word size for general arithmetic
- `ptr` / `uptr`: Pointer-sized integers for address arithmetic
- Width depends on target: 32-bit systems use i32/u32, 64-bit systems use i64/u64
- Use fixed-width types for struct fields, FFI, and message formats
- Use platform types for locals, loop indices, and counters

### Algebraic Data Types

ADTs are sum types that can have multiple variants, each optionally carrying a payload:

```oak
// Simple enum
Color: type = Red | Green | Blue

// With payloads
Result[T, E]: type =
  | Ok: T
  | Err: E

// With default values
StatusCode: type =
  | Ok: u16 = 200
  | NotFound: u16 = 404
  | ServerError: u16 = 500

// Record type (single variant)
Point: type = {
  x: i32
  y: i32
}
```

### Intersection Types

Oak supports intersection types for record composition:

```oak
Named: type = { name: string }
Aged: type = { age: i32 }

// Person is intersection of Named and Aged
Person: type = Named & Aged

// Employee extends Person
Employee: type = Person & { id: u32 }
```

**Important**: Intersection types are only allowed at type definition time. The resulting type is nominal (not structural), so there's no automatic subtyping.

### Phantom Types

Phantom types provide type-level distinctions with zero runtime cost:

```oak
// Phantom type parameter (unused at runtime)
Id[T]: type = u64

// Tag types
UserTag: type = {}
OrderTag: type = {}

// Type-safe IDs
User: type = {
  id: Id[UserTag]
  name: string
}

Order: type = {
  id: Id[OrderTag]
  amount: u32
}

// Type system prevents mixing UserTag and OrderTag IDs
fn process_user(id: Id[UserTag]): () {
  // Implementation
}

// process_user(user_id)  // OK
// process_user(order_id) // Type error!
```

### Generics

Oak supports parametric polymorphism with constraints:

```oak
// Generic type
Option[T]: type =
  | Some: T
  | None

// Generic function
fn map[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) => Option.Some(f(value))
    | Option.None => Option.None

// Generic with interface constraints
fn process[T: Readable & Writable](item: T): () {
  // T must implement both Readable and Writable
}
```

### Type Inference

Oak supports type inference for local variables:

```oak
// Type inferred from initial value
x := 42        // x: int
name := "Oak"  // name: string

// Explicit type annotation
y: i32 = 42
```

---

## Memory Management

### Ownership Model

Oak uses an ownership model similar to Rust, but simpler:

- **Owned arrays** `[N]T`: Own the memory
- **Views** `[]T`: Read-only borrows
- **Spans** `[*]T`: Writable borrows

### Borrow States

For each owned array, the borrow checker tracks:

- **Free**: No active borrows
- **SharedRead**: One or more read-only borrows (views)
- **UniqueWrite**: Exactly one writable borrow (span)

### Borrow Rules

1. **Many readers OR one writer**: You can have multiple views or one span, but not both
2. **Lexical scoping**: Borrows are tied to their block scope
3. **Region disjointness**: Multiple spans can coexist if their memory regions don't overlap

### Examples

```oak
// Multiple views allowed (read-only)
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }
v1: []u8 = arr[:]
v2: []u8 = arr[:]
x: u8 = v1[0]  // OK

// Single span (writable)
arr2: [4]u8 = [4]u8{ 10, 20, 30, 40 }
s: [*]u8 = span(&arr2)
s[0] = 100  // OK

// Cannot mix views and spans
// v3: []u8 = arr2[:]  // Error: owner is borrowed as span

// Lexical scoping
{
  v: []u8 = arr[:]
  // Use v
}  // v drops here; arr becomes free again

s2: [*]u8 = span(&arr)  // Now allowed
```

### Views and Spans

**Views** (`[]T`) are read-only borrows:
- Non-owning window into an existing buffer
- Can read elements but not modify
- Multiple views can coexist
- C representation: `{ const T* base; u32 len; }`

**Spans** (`[*]T`) are writable borrows:
- Non-owning window into an existing buffer
- Can read and write elements
- Must be unique (no overlapping spans)
- C representation: `{ T* base; u32 len; }`

---

## Advanced Features

### String Encodings

Oak treats encodings as first-class type-level capabilities:

```oak
// Encoding types
utf8: Encoding = {}
ascii: Encoding = {}
utf16: Encoding = {}
utf32: Encoding = {}

// Generic string types
Str[E: Encoding]: type = {
  bytes: []u8
}

StrBuf[E: Encoding]: type = {
  bytes: [*]u8
}

// Type aliases
string: type = Str[utf8]
string_buf: type = StrBuf[utf8]

// Encoding-tagged functions
fn write[E: Encoding](val: string): () {
  // Convert utf8 to encoding E and write
}

// Usage
write[ascii](msg)   // Converts UTF-8 to ASCII
write[utf8](msg)     // Writes UTF-8 directly
```

### String Functions

Oak provides encoding-aware string operations:

```oak
// Convert between encodings
fn into[E: Encoding](s: string): Str[E]
fn from_bytes[E: Encoding](b: []u8): Str[E]
fn recode[E: Encoding, F: Encoding](s: Str[E]): Str[F]

// Create strings from views
fn string_from_utf8(bytes: []u8): string

// Create mutable buffers from spans
fn buf_from_span[E: Encoding](span: [*]u8): StrBuf[E]
```

### Intrusive Data Structures

Oak supports zero-allocation intrusive data structures using phantom types and record composition:

```oak
// Phantom tag types
ReadyQueue: type = {}
IoQueue: type = {}

// Hook storage
ListHook[T, Tag]: type = {
  prev: Option[*T]
  next: Option[*T]
}

// Intrusive list container
IntrusiveList[T, Tag]: type = {
  head: Option[*T]
  tail: Option[*T]
}

// Task with multiple queue memberships
Task: type = {
  ready: ListHook[Task, ReadyQueue]
  io: ListHook[Task, IoQueue]
  id: u32
  name: string
}

// Interface for list operations
IntrusiveListNode[T, Tag]: interface =
  fn (self: *T) hook(_: Tag) -> *ListHook[T, Tag]

// Implement for each queue
fn (t: *Task) hook(_: ReadyQueue) -> *ListHook[Task, ReadyQueue] = &t.ready
fn (t: *Task) hook(_: IoQueue) -> *ListHook[Task, IoQueue] = &t.io

// Generic algorithm with intersection constraints
fn schedule[T: IntrusiveListNode[T, ReadyQueue]](
  runq: *IntrusiveList[T, ReadyQueue],
  task: *T
): () {
  // Add task to queue
}
```

This pattern provides:
- **Type safety**: Phantom tags prevent mixing different queue types
- **Zero allocation**: No extra allocations for list nodes
- **Multiple memberships**: One object can be in multiple lists
- **Clean C output**: Compiles to simple struct fields and pointers

### Struct Tags

Struct tags provide compile-time metadata on ADT variants and record fields:

```oak
// Tags on ADT variants
Status: type =
  | Ok: StatusPayload = { code: 200, msg: "Ok" }
      `{ name: "ok", category: "success" }`
  | NotFound: StatusPayload = { code: 404, msg: "Not Found" }
      `{ name: "not_found", category: "client_error" }`

// Tags on record fields
User: type = {
  id: u64 `{ db_column: "user_id", primary_key: 1 }`
  email: string `{ db_column: "email", unique: 1 }`
  age: u32 = 0 `{ db_column: "age", nullable: 1, unit: "years" }`
}
```

Tags are compile-time metadata only - they don't affect runtime layout. They can be used for:
- Database schema generation
- Serialization frameworks
- UI form generators
- Protocol documentation

---

## Compiler and Tooling

### Compilation Pipeline

Oak compiles through these stages:

1. **Scanner (Lexer)**: Tokenizes source code
2. **Parser**: Builds Abstract Syntax Tree (AST)
3. **Type Checker**: Performs type checking and inference
4. **Lowering**: Transforms AST to lowered form
5. **Borrow Checker**: Validates memory safety
6. **Code Generator**: Emits C code

### Code Generation

Oak generates readable, idiomatic C code:

```c
// Records compile to structs
typedef struct oak_Point {
  i32 x;
  i32 y;
} oak_Point;

// ADTs compile to enum + union
typedef enum oak_Option_i32_tag {
  oak_Option_i32_Some,
  oak_Option_i32_None
} oak_Option_i32_tag;

typedef struct oak_Option_i32 {
  u32 tag;
  union {
    i32 Some;
  } data;
} oak_Option_i32;

// Views compile to pointer + length
typedef struct oak_view_u8 {
  const u8* base;
  u32 len;
} oak_view_u8;

// Spans compile to pointer + length
typedef struct oak_span_u8 {
  u8* base;
  u32 len;
} oak_span_u8;
```

### C Style Rules

The code generator follows strict C style rules:

- Pointer asterisk belongs to the type: `u8* ptr`
- Opening brace on same line as header
- Space inside parentheses: `foo( x, y )`
- Consistent spacing and formatting

### Formatter

Oak includes a formatter that:

- Normalizes indentation and alignment
- Aligns tags across variants in the same ADT
- Aligns tags across fields in the same record
- Formats pattern matching arms consistently
- Handles both indentation-based and brace-based blocks

### REPL

Oak includes an interactive REPL with:

- Multiline input support (trailing `\` for continuation)
- Command history (up arrow for previous commands)
- Cursor movement (left/right arrows)
- REPL commands:
  - `:exit` / `:quit`: Exit REPL
  - `:help`: Show help
  - `:ptrsize(size)`: Set pointer size (32 or 64 bits)
  - `:intsize(size)`: Set integer size (32 or 64 bits)

---

## Examples

### Basic ADT Usage

```oak
Option[T]: type =
  | Some: T
  | None

Result[T, E]: type =
  | Ok: T
  | Err: E

// Pattern matching
maybe_int: Option[i32] = Option.Some(42)

value: i32 = maybe_int ?
  | Option.Some(x: i32) => x
  | Option.None => 0
```

### Generic Functions

```oak
fn map[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) => Option.Some(f(value))
    | Option.None => Option.None

// Usage
maybe_int: Option[i32] = Option.Some(5)
maybe_doubled: Option[i32] = map(maybe_int, fn(x: i32): i32 = x * 2)
```

### Borrow Checking

```oak
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// Multiple views allowed
v1: []u8 = arr[:]
v2: []u8 = arr[:]
x: u8 = v1[0]  // OK

// Single span
s: [*]u8 = span(&arr)
s[0] = 100  // OK

// Cannot mix
// v3: []u8 = arr[:]  // Error: owner is borrowed as span
```

### Platform Types with Arrays

```oak
// Use uint for loop indices and counters
fn sum_view(xs: []u8): uint = {
  acc: uint = 0
  i: uint = 0
  while i < len(xs) {
    acc = acc + uint(xs[i])
    i = i + 1
  }
  acc
}

// Low-level operations use uptr for addresses
fn c_memcpy(dst: *u8, src: *u8, n: uptr): () = unsafe {
  i: uptr = 0
  while i < n {
    *(*u8(uptr(dst) + i)) = *(*u8(uptr(src) + i))
    i = i + 1
  }
}
```

### Intrusive Lists

```oak
// See examples/intrusive_scheduler.oak for complete example
Task: type = {
  ready: ListHook[Task, ReadyQueue]
  id: u32
  name: string
}

fn (t: *Task) hook(_: ReadyQueue) -> *ListHook[Task, ReadyQueue] = &t.ready

fn schedule[T: IntrusiveListNode[T, ReadyQueue]](
  runq: *IntrusiveList[T, ReadyQueue],
  task: *T
): () {
  // Add task to queue
}
```

---

## Further Reading

- [A Tour of Oak](TOUR_OF_OAK.md) - Comprehensive language tour
- [Oak Specification](SPEC.md) - Complete language specification
- [Borrow Checker Specification](borrow_checker.md) - Memory safety rules
- [C Backend Specification](C_BACKEND_SPEC.md) - Code generation details
- [Intrusive Structures](INTRUSIVE_STRUCTURES.md) - Zero-allocation data structures
- [String Encoding Specification](STRINGS_ENCODING_SPEC.md) - Encoding system
- [Tagging and Labeling](TAGGING_AND_LABELING.md) - Struct tags and metadata

---

*Oak is actively developed. Check the latest documentation for updates and new features.*


## Native test tooling

`oak test` runs compiled unit tests, property tests, fuzz targets, and bounded
deterministic event simulations. See [the runner guide](testrunner/README.md)
and [the testing contract](docs/spec/110-testing.md) for examples, shrinking,
corpus replay, and Clang/libFuzzer harness export.
