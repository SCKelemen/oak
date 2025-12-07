# A Tour of Oak

Oak is a systems programming language with strong type safety, memory safety through borrow checking, and expressive type system features. This tour provides an overview of the language's major features.

## Table of Contents

1. [Packages](#packages)
2. [Imports](#imports)
3. [Comments](#comments)
4. [Variables and Types](#variables-and-types)
5. [Functions](#functions)
6. [Arithmetic and Operators](#arithmetic-and-operators)
7. [Pattern Matching](#pattern-matching)
8. [Algebraic Data Types (ADTs)](#algebraic-data-types-adts)
9. [Records](#records)
10. [Arrays, Slices, Views, and Spans](#arrays-slices-views-and-spans)
11. [Generics](#generics)
12. [Interfaces](#interfaces)
13. [Phantom Types](#phantom-types)
14. [Subtyping and Intersection Types](#subtyping-and-intersection-types)
15. [Borrow Checking](#borrow-checking)
16. [Control Flow](#control-flow)

---

## Packages

Every Oak program starts with a package declaration:

```oak
package main
```

```oak
package strings
```

The package name determines the namespace for your code.

---

## Imports

Oak supports importing packages in several ways:

```oak
// Import and bind to a variable
str := import("strings")

// Import with explicit type annotation
str: package = import("strings")

// Import multiple packages
import("strings", "encoding/utf8")

// Import without binding (for side effects)
import("strings")
```

---

## Comments

Oak supports both line and block comments:

```oak
// This is a line comment

/* This is an inline comment */

/* This is a 
   multi-line
   comment */
```

---

## Variables and Types

### Variable Declarations

Oak provides several ways to declare variables:

```oak
// With type annotation and initial value
x: i32 = 5

// With type annotation only (uninitialized)
y: i32

// Type inference (from initial value)
z := 10

// Explicit type annotation
name: string = "Oak"
```

### Primitive Types

Oak includes several primitive types:

- **Signed integers**: `i8`, `i16`, `i32`, `i64`
- **Unsigned integers**: `u8`, `u16`, `u32`, `u64`
- **Floating point**: `f32`, `f64` (if supported)
- **Boolean**: `Bool` (ADT, not primitive)
- **String**: `string`
- **Byte**: `byte` (alias for `u8`)

```oak
small: i8 = -128
large: i64 = 9223372036854775807
unsigned: u32 = 4294967295
text: string = "Hello, Oak!"
```

---

## Functions

Functions in Oak can be written in several styles:

```oak
// Single expression (no braces needed)
fn add(a: i32, b: i32): i32
  a + b

// Single expression with equals
fn add(a: i32, b: i32): i32 = a + b

// Block body
fn add(a: i32, b: i32): i32 {
  a + b
}

// Block body with equals
fn add(a: i32, b: i32): i32 = { a + b }
```

### Function Invocation

```oak
x: i32
sum: i32 = add(5, 3)
x = add(4, 2)
x = add(6, 4)  // reassignment
```

### Function Types

Function types use arrow syntax:

```oak
// Function type: (A, B) -> C
fn apply[A, B, C](f: (A) -> B, x: A): B = f(x)
```

### Methods

Functions can be associated with types using the `Type::Method` syntax:

```oak
File: type = {
  fd: u32
}

fn File::Read(self: File, dst: [*]u8): ReadResult =
  { n: 0, err: Option::None }
```

---

## Arithmetic and Operators

Oak supports standard arithmetic operations:

```oak
x: i32 = 5 + 3    // Addition
y: i32 = 10 - 2   // Subtraction
z: i32 = 4 * 2    // Multiplication
w: i32 = 8 / 2    // Division

// Comparison operators
eq: bool = 5 == 5
ne: bool = 5 != 3
lt: bool = 3 < 5

// String concatenation
greeting: string = "Hello" + ", " + "Oak!"
```

---

## Pattern Matching

Pattern matching is a core feature of Oak, using the `?` operator:

### Pattern Matching on Integers

```oak
x: i32 = 8

result: string = x ?
  | 5 -> "five"
  | 8 -> "eight"
  | _ -> "other"
```

### Pattern Matching on ADTs

```oak
Status: type = Ok | NotFound | Unauthorized

status: Status = Ok

code: i32 = status ?
  | Ok -> 200
  | NotFound -> 404
  | Unauthorized -> 401
  | _ -> 0
```

The `_` pattern matches anything (wildcard).

---

## Algebraic Data Types (ADTs)

ADTs allow you to define types with multiple variants:

### Simple ADT

```oak
Status: type = Ok | NotFound | Unauthorized
```

### ADT with Values

```oak
// ADT with integer literal tags
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// Create values
status1: Status = .Ok
status2: Status = .NotFound

// Pattern match to extract the value
code: i32 = status1 ?
  | .Ok -> 200
  | .NotFound -> 404
  | _ -> 0
```

### ADT with Record Literal Tags

```oak
StatusInfo: type
  = Ok: { code: 200, status: "Okay" }
  | NotFound: { code: 404, status: "Not Found" }

info: StatusInfo = .Ok
```

### ADT with Payloads

```oak
Option[T]: type = {
  Some: T
  None: {}
}

Result[T, E]: type = {
  Ok: T
  Err: E
}
```

### Generic ADTs

```oak
Option[T]: type = {
  Some: T
  None: {}
}

some_value: Option[i32] = Option::Some(42)
no_value: Option[i32] = Option::None
```

---

## Records

Records are product types (structs):

```oak
// Record type definition
Person: type = {
  name: string
  age: i32
}

// Record literal
sam: Person = { name: "Sam", age: 30 }

// Field access
name: string = sam.name
age: i32 = sam.age
```

### Empty Records

```oak
Unit: type = {}

value: Unit = {}
```

---

## Arrays, Slices, Views, and Spans

Oak provides several array-like types with different ownership semantics:

### Fixed Arrays

```oak
// Fixed-size array
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// Access elements
first: u8 = arr[0]
```

### Views (Read-only Slices)

Views (`[]T`) are read-only borrows of arrays:

```oak
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// Create a view
view: []u8 = arr[:]        // Full view
view2: []u8 = arr[1:3]     // Partial view
view3: []u8 = arr[2:]      // From index 2 to end
view4: []u8 = arr[:3]      // From start to index 3
```

### Spans (Writable Slices)

Spans (`[*]T`) are writable borrows:

```oak
arr: [4]u8 = [4]u8{ 10, 20, 30, 40 }

// Create a span
span: [*]u8 = span(&arr)
```

### Built-in Functions

```oak
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// Create views/spans
v: []u8 = view(&arr)
s: [*]u8 = span(&arr)

// Subslice operations
mid: []u8 = subslice(v, 1, 2)

// Reinterpretation
v2: []u8 = view_as(v)
s2: [*]u8 = span_as(s)
```

---

## Generics

Oak supports generic functions and types:

### Generic Functions

```oak
// Generic function
fn replicate4[T](value: T): [4]T = {
  xs: [4]T = [4]T{ value, value, value, value }
  xs
}

// Usage
four_ints: [4]i32 = replicate4(7)
four_strings: [4]string = replicate4("hello")
```

### Generic Types

```oak
Option[T]: type = {
  Some: T
  None: {}
}

Result[T, E]: type = {
  Ok: T
  Err: E
}

// Usage
maybe_int: Option[i32] = Option::Some(42)
maybe_string: Option[string] = Option::None
```

### Multiple Type Parameters

```oak
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option::Some(value: A) => Option::Some(f(value))
    | Option::None => Option::None
```

---

## Interfaces

Interfaces define method sets that types can implement:

### Interface Definition

```oak
ReadResult: type = { n: u64, err: Option[Error] }

Reader: interface = {
  Read: ([]u8) -> ReadResult
}

Writer: interface = {
  Write: ([]u8) -> WriteResult
}
```

### Implementing Interfaces

Types implicitly implement interfaces if they have matching methods:

```oak
File: type = {
  fd: u32
  closed: Bool
}

// File implements Reader because it has a Read method
fn File::Read(self: File, dst: [*]u8): ReadResult =
  { n: 0, err: Option::None }
```

### Constrained Generics

```oak
fn use_reader[R: Reader](r: R): u64 =
  r.Read([]u8{ 0, 0, 0, 0 }).n

// File can be used where Reader is required
f: File = { fd: 3, closed: Bool::False({}) }
bytes_read: u64 = use_reader(f)
```

### Interface Composition

```oak
ReadWriteCloser: type = Reader & Writer & Closer

fn safe_close_all[T: ReadWriteCloser](x: T): () =
  x.Close()
```

---

## Phantom Types

Phantom types use type parameters that don't appear at runtime, providing compile-time type safety:

```oak
// Phantom-parameterised ID
Id[T]: type = u64

UserTag: type = {}
OrderTag: type = {}

user_id: Id[UserTag] = 1
order_id: Id[OrderTag] = 2

// Type-safe comparison
fn same_user(a: Id[UserTag], b: Id[UserTag]): bool =
  a == b

// This would be a type error:
// same_user(user_id, order_id)  // Error: type mismatch
```

### Phantom Types with Arrays

```oak
Utf8: type = {}
Ascii: type = {}

Encoded[Tag]: type = { bytes: []u8 }

// Type-safe conversions
fn to_ascii(s: Encoded[Utf8]): Encoded[Ascii] =
  { bytes: s.bytes }
```

---

## Subtyping and Intersection Types

Oak supports structural subtyping through intersection types:

### Intersection Types

```oak
Named: type = { name: string }
Aged: type = { age: i32 }

// Person is the intersection of Named and Aged
Person: type = Named & Aged

// Employee extends Person
Employee: type = Person & { id: u32 }

// Subtyping: Employee <: Person <: Named
sam: Employee = { name: "Sam", age: 30, id: 1 }

// Can use Employee where Named is expected
fn greet_named(x: Named): string =
  "Hello, " + x.name

greeting: string = greet_named(sam)  // Works!
```

### Sum Types and Intersections

```oak
Color: type = Red | Green | Blue
PrimaryColor: type = Red | Blue

Colored: type = { color: Color }
NamedColored: type = Named & Colored

shirt: NamedColored = { name: "shirt", color: Red }
```

---

## Borrow Checking

Oak's borrow checker ensures memory safety without garbage collection:

### Basic Rules

1. **Many readers OR one writer**: You can have multiple views (read-only) or one span (writable), but not both.
2. **Lexical scoping**: Borrows are tied to their block scope.
3. **Region disjointness**: Multiple spans can coexist if their memory regions don't overlap.

### Example: Multiple Views

```oak
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }

// Multiple views are allowed (read-only)
v1: []u8 = arr[:]
v2: []u8 = arr[:]

x1: u8 = v1[0]
x2: u8 = v2[1]
x3: u8 = arr[2]  // Can still read from owner
```

### Example: Single Span

```oak
arr: [4]u8 = [4]u8{ 10, 20, 30, 40 }

// One span (writable)
s: [*]u8 = span(&arr)

y1: u8 = s[0]
y2: u8 = s[1]

// Cannot use arr directly after creating span
// arr[0]  // Error: owner is borrowed
```

### Example: Lexical Scoping

```oak
arr: [4]u8 = [4]u8{ 5, 6, 7, 8 }

{
  v: []u8 = arr[:]
  tmp: u8 = v[0]
}  // v drops here; arr becomes free again

s: [*]u8 = span(&arr)  // Now allowed
z: u8 = s[1]
```

### Example: Slicing

```oak
arr: [6]u8 = [6]u8{ 0, 1, 2, 3, 4, 5 }

// Slicing creates views
sub1: []u8 = arr[1:4]
sub2: []u8 = arr[2:]
sub3: []u8 = arr[:4]
sub4: []u8 = arr[:]

// Subslice of an existing view
sub1_inner: []u8 = sub1[0:2]
```

---

## Control Flow

### While Loops

```oak
i: i32 = 0
while i < 10 {
  // loop body
  i = i + 1
}
```

### Pattern Matching as Control Flow

Pattern matching can be used for conditional logic:

```oak
result: Option[i32] = Option::Some(42)

value: i32 = result ?
  | Option::Some(x: i32) => x
  | Option::None => 0
```

---

## Advanced Examples

### Generic Map Function

```oak
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option::Some(value: A) => Option::Some(f(value))
    | Option::None => Option::None

// Usage
maybe_int: Option[i32] = Option::Some(5)
maybe_doubled: Option[i32] = map_option(maybe_int, fn(x: i32): i32 = x * 2)
```

### Result Type for Error Handling

```oak
Result[T, E]: type = {
  Ok: T
  Err: E
}

fn bind_result[A, B, E](
  res: Result[A, E], 
  f: (A) -> Result[B, E]
): Result[B, E] =
  res ?
    | Result::Ok(value: A) => f(value)
    | Result::Err(err: E) => Result::Err(err)
```

### Interface with Generics

```oak
TextReader[T]: interface = {
  ReadChunk: ([]) -> TextChunk[T]
}

fn read_one_chunk[R, Tag](r: R): Encoded[Tag]
  where R: TextReader[Tag] =
{
  chunk: TextChunk[Tag] = r.ReadChunk([])
  chunk.data
}
```

---

## Next Steps

- Read the [Oak Specification](SPEC.md) for complete language details
- Check [Implementation Status](IMPLEMENTATION_STATUS.md) to see what's implemented
- Explore the [examples](examples/) directory for more code samples

---

*This tour covers the major features of Oak. The language continues to evolve, so check the latest documentation for updates.*
