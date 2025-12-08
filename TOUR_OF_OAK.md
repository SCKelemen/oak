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
// Import and rename
str := import("strings")

// Import with explicit type annotation (you would never do this)
str: package = import("strings")

// Import multiple packages
import("strings", "encoding/utf8")

// Import without binding (imported with default package name)
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
- **Platform types**: `int`, `uint`, `ptr`, `uptr`
- **Floating point**: `f32`, `f64` (if supported)
- **Boolean**: `Bool` (ADT, not primitive)
- **String**: `string`
- **Byte**: `byte` (alias for `u8`)
- **Rune**: `rune` (alias for `i32`)

```oak
small: i8 = -128
large: i64 = 9223372036854775807
unsigned: u32 = 4294967295
text: string = "Hello, Oak!"

// Underscores in numeric literals for readability
large: i64 = 922_337_203_685_477_5807
count: u32 = 2_000_000
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

```oak
// Untyped integer literals default to int
a := 5        // a: int = 5 (on 64-bit: i64, on 32-bit: i32)
b: uint = 6   // b: uint = 6

// Type constructors support all types
x: int = int(42)
y: uint = uint(100)
addr: uptr = uptr(16r1000)  // hex: 4096 in decimal
offset: ptr = ptr(-4)
```

### Radix-Based Numeric Literals

Oak supports radix-based numeric literals for bases 2-16 using the format `BASErDIGITS`:

```oak
// Binary (base 2)
bin: int = 2r1010        // 10 in decimal

// Octal (base 8)
oct: int = 8r777         // 511 in decimal

// Decimal (base 10) - explicit
dec: int = 10r9999       // 9999 in decimal

// Hexadecimal (base 16)
hex: int = 16rFFFF       // 65535 in decimal
addr: uptr = uptr(16r1000)  // 4096 in decimal

// Other bases (11-16 use A-F for digits 10-15)
base11: int = 11rAAAA    // 14640 in decimal
base12: int = 12rBBBB    // 20735 in decimal
base13: int = 13rCCCC
base14: int = 14rDDDD
base15: int = 15rEEEE

// Underscores are supported in radix literals too
large_hex: int = 16rFF_FF_FF_FF  // 4294967295
```

---

## Functions

Functions in Oak can be written in several styles:

```oak
// Single expression (no braces needed)
// "ExpressionBodiedFunction"
fn add(a: i32, b: i32): i32
  a + b

// Single expression with equals
// "inline ExpressionBodiedFunction"
fn add(a: i32, b: i32): i32 = a + b

// Block body
// "BlockBodiedFunction"
fn add(a: i32, b: i32): i32 {
  a + b
}

// Block body with equals
// "inline BlockBodiedFunction"
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

Functions are associated with types using Go-style method binding (receiver syntax):

```oak
File: type = {
  fd: u32
}

fn (self: File) Read(dst: [*]u8): ReadResult =
  { n: 0, err: Option.None }
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
gt: bool = 3 > 5
lte: bool = 3 <= 5
gte: bool = 3 >= 5

// there is a built in comparoson type
Comparison: type = 
    | Less: -1
    | Equal: 0
    | Greater: 1

// String concatenation
greeting: string = strings.join("Hello", ", ", "Oak!")
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

Oak supports both `->` and `=>` for pattern matching arms:

```oak
Status: type = Ok | NotFound | Unauthorized

status: Status = Ok

// Using -> (arrow syntax)
code: i32 = status ?
  | Ok -> 200
  | NotFound -> 404
  | Unauthorized -> 401
  | _ -> 0

// Using => (fat arrow syntax, equivalent)
code2: i32 = status ?
  | Ok => 200
  | NotFound => 404
  | Unauthorized => 401
  | _ => 0
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
Option[T]: type = Some[T] | None

// also equivalent 
Option[T]: type = Some[T]
                | None

some_value: Option[i32] = Option.Some(42)
no_value: Option[i32] = Option.None
```


### ADT Zoo 

```oak
Color: type = Red | Green | Blue
Color: type = | Red | Green | Blue
Color := Red | Green | Blue
Color := Red | Green | Blue

Color: type = Red 
            | Green
            | Blue

Color: type =
            | Red 
            | Green
            | Blue

Color := Red 
       | Green
       | Blue

Color :=
      | Red 
      | Green
      | Blue


fn color_to_string(c: Color): string {
  c ?
    | Red => "red"
    | Green => "green"
    | Blue => "blue"
    | _ => "unreachable"
}      

fn color_to_string(c: Color): string = c ? Red => "red" | Green => "green" | Blue => "blue" | _ => "unreachable"
fn color_to_string(c: Color): string = c ? | Red => "red" | Green => "green" | Blue => "blue" | _ => "unreachable"

fn color_to_string(c: Color): string {
  c ?
    | .Red => "red"
    | .Green => "green"
    | .Blue => "blue"
    | _ => "unreachable"
}      

fn color_to_string(c: Color): string = c ? .Red => "red" | .Green => "green" | .Blue => "blue" | _ => "unreachable"
fn color_to_string(c: Color): string = c ? | .Red => "red" | .Green => "green" | .Blue => "blue" | _ => "unreachable"


fn color_to_string(c: Color): string {
  c ?
    | Color.Red => "red"
    | Color.Green => "green"
    | Color.Blue => "blue"
    | _ => "unreachable"
}      

fn color_to_string(c: Color): string = c ? Color.Red => "red" | Color.Green => "green" | Color.Blue => "blue" | _ => "unreachable"
fn color_to_string(c: Color): string = c ? | Color.Red => "red" | Color.Green => "green" | Color.Blue => "blue" | _ => "unreachable"

// the canonical form for the formatter are
// full block
fn color_to_string(c: Color): string {
  c ?
    | .Red   => "red"
    | .Green => "green"
    | .Blue  => "blue"
    | _      => "unreachable"
}      
// inline expression
fn color_to_string(c: Color): string = c ? .Red => "red" | .Green => "green" | .Blue => "blue" | _ => "unreachable"
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


ABCD: type = {
  A: u32
  B: u32
  C: u32
  D: u32
}

example := ABCD{
  A: 0,
  B: 1,
  C: 2,
  D: 3, // trailing comma is allowed
}

example2 := ABCD{ A: 0, B: 1, C: 2, D: 3 }
example3: ABCD = 
               { A: 0
               , B: 1
               , C: 2
               , D: 3 
               }


example3 := 
      ABCD{ A: 0
          , B: 1
          , C: 2
          , D: 3 
          }
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
maybe_int: Option[i32] = Option.Some(42)
maybe_string: Option[string] = Option.None
```

### Multiple Type Parameters

```oak
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) => Option.Some(f(value))
    | Option.None => Option.None

// Both -> and => work in pattern matching
fn map_option2[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) -> Option.Some(f(value))
    | Option.None -> Option.None
```

---

## Interfaces

Interfaces define method sets that types can implement:

### Interface Definition

Interfaces can be defined using either function-style or label-style syntax:

```oak
ReadResult: type = { n: u64, err: Option[Error] }
WriteResult: type = { n: u64, err: Option[Error] }

// Function-style syntax (method signature without receiver)
Reader: interface = {
  Read([]u8) -> ReadResult
}

// Label-style syntax (method name as label)
Writer: interface = {
  Write: ([]u8) -> WriteResult
}

// Both styles can be mixed in the same interface
ReadWriter: interface = {
  Read([]u8) -> ReadResult
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

// File implements Reader because it has a Read method with the correct signature
fn (self: File) Read(dst: [*]u8): ReadResult =
  { n: 0, err: Option.None }
```

### Constrained Generics

Interface constraints use `:` syntax directly in the type parameter list (no `where` keyword):

```oak
fn use_reader[R: Reader](r: R): u64 =
  r.Read([]u8{ 0, 0, 0, 0 }).n

// File can be used where Reader is required
f: File = { fd: 3, closed: .False }
// equivalent
f: File = { fd: 3, closed: Bool.False }
bytes_read: u64 = use_reader(f)
```

### Interface Composition

```oak
ReadWriteCloser: type = Reader & Writer & Closer

// Constraints with intersection types
fn safe_close_all[T: ReadWriteCloser](x: T): () =
  x.Close()

// Multiple constraints using intersection
fn copy_all[R: Reader, W: Writer](src: R, dst: W): u64 =
  { total: u64 = 0; total }
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

### Intrusive Data Structures

Oak's type system enables type-safe intrusive data structures using interfaces, type intersections, and phantom tags. This pattern allows objects to participate in multiple data structures without extra allocations:

```oak
// Phantom tags for different queue types
ReadyQueue: type = {}
IoQueue: type = {}
TimerQueue: type = {}

// Hook storage for list membership
ListHook[T, Tag]: type = {
  prev: Option[*T]
  next: Option[*T]
}

// Intrusive list container
IntrusiveList[T, Tag]: type = {
  head: Option[*T]
  tail: Option[*T]
}

// Interface: "T can provide its hook for list Tag"
// Using function-style syntax
IntrusiveListNode[T, Tag]: interface = {
  fn (self: *T) hook(_: Tag) -> *ListHook[T, Tag]
}

// Task that can be in multiple queues simultaneously
Task: type = {
  ready: ListHook[Task, ReadyQueue]
  io: ListHook[Task, IoQueue]
  timer: ListHook[Task, TimerQueue]
  id: u32
  name: string
}

// Implement interfaces for each queue using Go-style method binding
fn (t: *Task) hook(_: ReadyQueue): *ListHook[Task, ReadyQueue] =
  &t.ready

fn (t: *Task) hook(_: IoQueue): *ListHook[Task, IoQueue] =
  &t.io

fn (t: *Task) hook(_: TimerQueue): *ListHook[Task, TimerQueue] =
  &t.timer

// Generic function with single constraint
fn schedule[T: IntrusiveListNode[T, ReadyQueue]](
  runq: *IntrusiveList[T, ReadyQueue],
  task: *T
): () = {
  // Implementation would push task to queue
}

// Generic function with intersection constraints (multiple list memberships)
fn park_in_io_and_timer[
  T: IntrusiveListNode[T, IoQueue] & IntrusiveListNode[T, TimerQueue]
](
  ioq: *IntrusiveList[T, IoQueue],
  tq: *IntrusiveList[T, TimerQueue],
  task: *T
): () = {
  // Implementation would add task to both queues
}
```

This pattern provides:
- **Type safety**: Phantom tags prevent mixing different queue types
- **Zero allocation**: No extra allocations for list nodes
- **Multiple memberships**: One object can be in multiple lists
- **Clean C output**: Compiles to simple struct fields and pointers

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
  strings.join("Hello, ", x.name)

greeting: string = greet_named(sam)  // Works!
```

### Sum Types and Intersections

```oak
Color: type = Red | Green | Blue
PrimaryColor: type = Red | Blue

Colored: type = { color: Color }
NamedColored: type = Named & Colored

shirt: NamedColored = { name: "shirt", color: Red }
// equivalent 
shirt: NamedColored = { name: "shirt" } & { color: Red }
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
result: Option[i32] = Option.Some(42)

value: i32 = result ?
  | Option.Some(x: i32) => x
  | Option.None => 0

// Type matching (both -> and => work)
value ? 
  | _: string -> "string"
  | _: i32 -> "i32"
  | _: any -> "anything else"

value ? 
  | _: string => "string"
  | _: i32 => "i32"
  | _ => "anything else"      

// Capturing values in type patterns
value ? 
  | captured: string -> strings.join("string was ", captured)
  | captured: i32 -> strings.join("i32 was ", string(captured))
  | _ -> "wildcard"
```

---

## Advanced Examples

### Generic Map Function

```oak
fn map_option[A, B](opt: Option[A], f: (A) -> B): Option[B] =
  opt ?
    | Option.Some(value: A) => Option.Some(f(value))
    | Option.None => Option.None

// Usage
maybe_int: Option[i32] = Option.Some(5)
maybe_doubled: Option[i32] = map_option(maybe_int, fn(x: i32): i32 = x * 2)
```

### Result Type for Error Handling

```oak
// result is a union type
Result[T, E]: type = 
                   | Ok: T
                   | Err: E


fn bind_result[A, B, E](
  res: Result[A, E], 
  f: (A) -> Result[B, E]
): Result[B, E] =
  res ?
    | Result.Ok(value: A) => f(value)
    | Result.Err(err: E) => Result.Err(err)

// Both -> and => are equivalent in pattern matching
fn bind_result2[A, B, E](
  res: Result[A, E], 
  f: (A) -> Result[B, E]
): Result[B, E] =
  res ?
    | Result.Ok(value: A) -> f(value)
    | Result.Err(err: E) -> Result.Err(err)
```

### Interface with Generics

```oak
TextChunk[T]: type = { data: Encoded[T], eof: Bool }

TextReader[T]: interface = {
  ReadChunk: ([]) -> TextChunk[T]
}

// Constraints go directly in the type parameter list (no where clause)
fn read_one_chunk[R: TextReader[Tag], Tag](r: R): Encoded[Tag] = {
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
