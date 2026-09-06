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
