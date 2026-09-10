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

main: (): i32 {
  z: i32 = x + y
  z
}
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

// ADT definition with value
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

main: (): i32 {
  y: i32 = x * 2

  // Pattern matching on integers
  result: string = x ?
    | 5 -> "five"
    | 8 -> "eight"
    | _ -> "other"

  // Create ADT values
  status1: Status = .Ok
  status2: Status = .NotFound

  // Pattern match on ADT
  code: i32 = status1 ?
    | .Ok -> 200
    | .NotFound -> 404
    | _ -> 0
  y + code
}
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

main: (): i32 {
  result: i32 = scale(3, 4)
  result
}
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

main: (): i32 {
  total: i32 = countdown(10, 0)
  total
}
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

main: (): i32 {
  result: i32 = fact(5, 1)
  result
}
`,
		},
		{
			// Span writes: bounds-checked stores through writable spans,
			// symmetric with the loads; views are read-only at type level.
			Name: "span_write",
			SourceCode: `
fill: (s: [*]u8): i32 {
  n: u32 = len(s)
  i: u32 = 0
  while i < n {
    s[i] = u8(7)
    i = i + 1
  }
  i32(s[0]) + i32(s[3])
}

main: (): i32 {
  data: [4]u8
  s: [*]u8 = span(&data)
  fill(s)
}
`,
		},
		{
			// ADT construction and tag-guarded match lowering, including a
			// variant-arm tail call lowered to a loop.
			Name: "adt_match",
			SourceCode: `
Shape: type =
  | Circle: i32
  | Square: i32
  | Empty

area2: (s: Shape): i32 = s ?
  | .Circle(r) -> r * 3
  | .Square(w) -> w * w
  | .Empty -> 0

main: (): i32 {
  c: Shape = .Circle(5)
  q: Shape = .Square(4)
  area2(c) + area2(q)
}
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

main: (): i32 {
  v: i32 = checked_double(21)
  v
}
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
			// The C interface library (docs/spec/92-ffi.md): an extern
			// binding declares the foreign symbol it asserts, calls use the
			// raw symbol, and c conversions are explicit casts.
			Name: "c_ffi",
			SourceCode: `
putchar: (ch: c.Int): c.Int = c.extern("putchar")

main: (): i32 {
  putchar(c.Int(79))
  putchar(c.Int(10))
  0
}
`,
		},
		{
			// Floating point (docs/spec/20-types.md section 11.3): contextual
			// literals, plain-operator arithmetic under FP_CONTRACT OFF,
			// correctly rounded intrinsics, and bit-pattern observation.
			Name: "floats",
			SourceCode: `
norm: (x: f32, y: f32): f32 {
  sqrt(x * x + y * y)
}

main: (): i32 {
  n: f32 = norm(3.0, 4.0)
  bits: u32 = u32_bits_f32(n)
  half: f64 = f64(n) * 0.5
  bits == u32(1084227584) && half == 2.5 ? 0 | 1
}
`,
		},
		{
			// Spans at the boundary (docs/spec/92-ffi.md section 2.5): a view
			// crosses as its base pointer and element count for one call,
			// and c.String hands C a NUL-terminated literal.
			Name: "c_ffi_spans",
			SourceCode: `
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")
puts: (s: c.String): c.Int = c.extern("puts")

emit: (bytes: []u8): () {
  _ = write(c.Int(1), c.span_of(bytes))
}

main: (): i32 {
  text: []u8 = str_bytes("OK")
  emit(text)
  _ = puts(c.String(""))
  0
}
`,
		},
		{
			// arm64 instruction functions (docs/spec/92-ffi.md section 3):
			// the instruction on AArch64 targets, the proven-equivalent
			// portable sequence elsewhere, one helper per intrinsic.
			Name: "arm64_intrinsics",
			SourceCode: `
main: (): i32 {
  assert(arm64.clz32(u32(0)) == u32(32))
  assert(arm64.rev32(arm64.rev32(u32(287454020))) == u32(287454020))
  assert(arm64.rbit64(arm64.rbit64(u64(9))) == u64(9))
  0
}
`,
		},
		{
			// Portable SIMD (docs/spec/93-simd.md): the byte-search kernel
			// (load, splat, eq, any), a vector store through a span, and an
			// arm64 horizontal reduction — usage-gated helper emission with
			// NEON and portable branches.
			Name: "simd_kernel",
			SourceCode: `
contains16: (v: []u8, needle: u8): Bool {
  chunk: simd.U8x16 = simd.load_u8x16(v, u32(0))
  hits: simd.U8x16 = simd.eq_u8x16(chunk, simd.splat_u8x16(needle))
  simd.any_u8x16(hits)
}

main: (): i32 {
  out: [16]u8
  s: [*]u8 = span(&out)
  simd.store_u8x16(s, u32(0), simd.splat_u8x16(u8(66)))
  assert(arm64.uaddlv_u8x16(simd.splat_u8x16(u8(1))) == u32(16))
  i32(s[0])
}
`,
		},
		{
			// Records end to end (docs/spec/40-records.md): struct typedefs
			// in declaration order with the proven natural layout
			// (Oak.RecordLayoutRefinement) enforced by static assertions,
			// compound-literal construction, and field access. Includes the
			// colon-less definition form (docs/spec/10-syntax.md section 3).
			Name: "records",
			SourceCode: `
Point: type = struct {
  x: i32
  y: i32
}

Pair: type = struct {
  first: Point
  tag: u8
}

shift(p: Point, dx: i32): Point = Point { x: p.x + dx, y: p.y }

main: (): i32 {
  p: Point = Point { x: 11, y: 31 }
  pair: Pair = Pair { first: shift(p, 9), tag: u8(3) }
  pair.first.x + i32(pair.tag)
}
`,
		},
		{
			// Conditionals are matches (docs/spec/10-syntax.md §3a): the Bool
			// condition sugar in statement position (lowered to C if/else),
			// short-circuit connectives, and total explicit conversions
			// (docs/spec/20-types.md). No if/else keywords exist.
			Name: "conditionals",
			SourceCode: `
classify: (n: i32, urgent: Bool): i32 {
  result: i32 = i32(u8_saturating_u32(u32(300)))
  n < 0 && !urgent ? {
    result = 0 - 1
  } | {
    n == 0 || urgent ? {
      result = i32_bits_u32(u32(1))
    }
  }
  result
}

main: (): i32 = classify(5, false)
`,
		},
		{
			// Generic ADT monomorphization (codegen/mono.go): two
			// instantiations of one template get separate specialized tagged
			// unions, variant construction and matching resolve
			// type-directed via the checker's records, and checked
			// narrowing returns a monomorphized Result.
			Name: "generic_adt",
			SourceCode: `
Overflow: type = | Overflow

Result[T, E]: type = Ok: T | Err: E

Option[T]: type = Some: T | None

first_even: (a: u32, b: u32): Option[u32] {
  a - (a / u32(2)) * u32(2) == u32(0) ? { .Some(a) } | {
    b - (b / u32(2)) * u32(2) == u32(0) ? { .Some(b) } | { .None }
  }
}

main: (): i32 {
  found: Option[u32] = first_even(u32(3), u32(8))
  byteRange: i32 = u8_checked_u32(u32(300)) ?
    | .Ok(v) => i32(v)
    | .Err(e) => 0 - 1
  found ?
    | .Some(n) => i32_bits_u32(n) + byteRange
    | .None => byteRange
}
`,
		},
		{
			// Const parameters and generic records (docs/spec/20-types.md,
			// docs/spec/40-records.md): Ring[T, N] as a zero-initialized
			// static global with field mutation, array-field stores through
			// the proven layout, and % arithmetic.
			Name: "ring_buffer",
			SourceCode: `
Ring[T, N: u32]: type = struct {
  buffer: [N]T
  head: u32
  count: u32
}

events: Ring[u8, 8]

push: (v: u8): () {
  events.buffer[(events.head + events.count) % u32(8)] = v
  events.count = events.count + 1
}

main: (): i32 {
  push(u8(7))
  i32(events.buffer[events.head]) + i32_bits_u32(events.count)
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
