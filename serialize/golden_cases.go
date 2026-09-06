package serialize

// GoldenCase is one end-to-end golden corpus program: every compiler stage's
// output for it is captured under golden/ and verified by the corpus test.
type GoldenCase struct {
	Name       string
	SourceCode string
	Skip       bool // Skip if known to have issues
}

// GoldenCases is the single authoritative corpus list, shared by
// cmd/generate_golden, cmd/verify_golden, and the golden corpus test.
func GoldenCases() []GoldenCase {
	return []GoldenCase{
		{
			Name: "simple",
			SourceCode: `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`,
		},
		{
			Name: "type_errors",
			SourceCode: `
x: i32 = "hello"
y: string = 42
`,
		},
		{
			Name: "simple_arithmetic",
			SourceCode: `
// Simple arithmetic
x: i32 = 5 + 3
y: i32 = x * 2

// Pattern matching on integers
result: string = x ?
  | 5 -> "five"
  | 8 -> "eight"
  | _ -> "other"

// ADT definition with value
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// Create ADT values
status1: Status = .Ok
status2: Status = .NotFound

// Pattern match on ADT
code: i32 = status1 ?
  | .Ok -> 200
  | .NotFound -> 404
  | _ -> 0
`,
		},
		{
			Name: "simple_function",
			SourceCode: `
fn add(a: i32, b: i32): i32
  a + b

fn add2(a: i32, b: i32): i32 = a + b

fn add3(a: i32, b: i32): i32 {
  a + b
}

fn add4(a: i32, b: i32): i32 = { a + b }

x: i32
sum: i32 = add(5, 3)
x = add(4, 2)
x = add(6, 4)
`,
		},
		{
			Name: "adt_with_values",
			SourceCode: `
// Simple ADT
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// ADT with record literal tags
StatusInfo: type
  = Ok: { code: 200, status: "Okay" }
  | NotFound: { code: 404, status: "Not Found" }
`,
		},
		{
			Name: "package_import",
			SourceCode: `
package main

import("strings")

str := import("strings")

str2: package = import("strings")

import("strings", "encoding/utf8")
`,
		},
		{
			Name: "comments",
			SourceCode: `
// line comment
x: i32 = 5

/* inline comment */
y: i32 = 10

/* multiple
    line
    comment
*/
z: i32 = 15
`,
		},
		{
			// Function block bodies retain every statement (ast.BlockExpression):
			// the local declaration must survive into checking and codegen.
			Name: "block_body_function",
			SourceCode: `
fn scale(a: i32, b: i32) -> i32 {
  doubled: i32 = a * 2
  doubled + b
}

result: i32 = scale(3, 4)
`,
		},
		{
			// Self tail recursion compiles to a loop (docs/spec/85-discipline.md):
			// the C output must contain the loop lowering, not a recursive call.
			Name: "tail_recursion",
			SourceCode: `
fn countdown(n: i32, acc: i32) -> i32 {
  countdown(n - 1, acc + n)
}

total: i32 = countdown(10, 0)
`,
		},
		{
			// Terminating recursion: base case + tail call in a lowerable-shape
			// match compiles to a loop with a guarded return.
			Name: "factorial",
			SourceCode: `
fn fact(n: i32, acc: i32) -> i32 {
  n ?
    | 0 -> acc
    | _ -> fact(n - 1, acc * n)
}

result: i32 = fact(5, 1)
`,
		},
		{
			// Canonical declaration-form functions (10-syntax section 3):
			// a name bound to a function interface and a definition.
			Name: "function_binding",
			SourceCode: `
addi32: (a, b: i32): i32 = a + b

scale: (base: i32, factor, offset: i32) -> i32 {
  addi32(base * factor, offset)
}

fact: (n, acc: i32): i32 = n ?
  | 0 -> acc
  | _ -> fact(n - 1, acc * n)
`,
		},
		{
			// Bounds-checked element access: views index through a trapping
			// helper, owned arrays through a static-length guard; len lowers
			// to constants or the len field (50-borrowing: never UB).
			Name: "indexing",
			SourceCode: `
fn sum(buf: [8]u8) -> u32 {
  v: []u8 = buf[0:8]
  n: u32 = len(v)
  total: u32 = 0
  i: u32 = 0
  while i < n {
    total = total + u32(v[i])
    i = i + 1
  }
  total + u32(buf[0]) + len(buf)
}
`,
		},
		{
			// Variadic trailing parameters: the call site materializes a
			// caller-owned stack array and passes a view (docs/spec/10-syntax.md).
			Name: "variadic",
			SourceCode: `
fn total(base: i32, rest: ...i32) -> i32 {
  base
}

fn caller() -> i32 {
  total(1, 2, 3)
}
`,
		},
		{
			// is_valid_utf8: zero-allocation validation against the proven
			// Oak.Utf8Validity brackets, lowered to a C runtime helper.
			Name: "utf8_check",
			SourceCode: `
fn all_text(buf: [16]u8) -> Bool {
  v: []u8 = buf[0:16]
  is_valid_utf8(v)
}
`,
		},
		{
			// The canonical bounded loop shape (docs/spec/85-discipline.md
			// section 3) carries its own static iteration bound.
			Name: "bounded_loop",
			SourceCode: `
total: i32 = 0
i: i32 = 0
while i < 10 {
  total = total + i
  i = i + 1
}
`,
		},
		{
			// assert is always compiled in (docs/spec/85-discipline.md section 5).
			Name: "assertions",
			SourceCode: `
fn checked_double(n: i32) -> i32 {
  assert(n < 100)
  n * 2
}

v: i32 = checked_double(21)
`,
		},
		{
			// Mutual tail recursion with matching signatures compiles to one
			// trampoline engine (docs/spec/85-discipline.md): the whole cycle
			// runs in a single frame.
			Name: "mutual_tail_recursion",
			SourceCode: `
fn ping(n: i32) -> i32 {
  x: i32 = n + 1
  pong(x)
}

fn pong(n: i32) -> i32 {
  y: i32 = n * 2
  ping(y)
}
`,
		},
		{
			// Unsafe boundary: unprovable span overlap is admitted inside unsafe
			// as a recorded OAK-B0110 assumption (warning), not an error.
			Name: "unsafe_block",
			SourceCode: `
buf: [16]u8
unsafe {
  a: [*]u8 = span(&buf)
  b: [*]u8 = span(&buf)
}
`,
		},
	}
}
