package lean

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func extract(t *testing.T, src string) (string, error) {
	t.Helper()
	p := parser.New(scanner.New(src))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse: %v", p.Errors())
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("typecheck: %v", errs)
	}
	return Emit(program, tc, "Test", nil)
}

// The translation's shape (docs/spec/95-extraction.md): fixed-width
// integers are Lean UInts, arrays are Arrays, a span parameter is returned
// with the result, a while loop is a fuel-indexed helper over the outer
// variables it reads and writes, a conditional rebinds what its arms assign.
func TestExtractionShape(t *testing.T) {
	src := `
Pair: type = struct { lo: u32, hi: u32 }
fill: (dst: [*]u8, n: u32): u32 {
  i: u32 = 0
  while i < n && i < len(dst) {
    dst[i] = u8_trunc_u32(i)
    i = i + u32(1)
  }
  i
}
classify: (v: []u8, at: u32): Pair {
  p: Pair = Pair { lo: u32(0), hi: u32(0) }
  v[at] < u8(128) ? { p.lo = u32(1) } | { p.hi = u32(1) }
  p
}
`
	_ = src
	// u8_trunc_u32 is a conversion outside the first subset; use a
	// widening instead so the program stays inside it.
	src = strings.Replace(src, "u8_trunc_u32(i)", "u8(7)", 1)
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"structure Pair where\n  lo : UInt32\n  hi : UInt32\n  deriving Repr, Inhabited, BEq",
		"def fill.loop1 (dst : Array UInt8) (n : UInt32) (i : UInt32) : Nat → Option (Array UInt8 × UInt32)",
		"  | 0 => none",
		"if ((decide (i < n)) && (decide (i < (dst.size.toUInt32)))) then do",
		"let dst := dst.setIfInBounds i.toNat (7 : UInt8)",
		"fill.loop1 dst n i fuel",
		"def fill (dst : Array UInt8) (n : UInt32) (fuel : Nat) : Option (UInt32 × Array UInt8) := do",
		"let (dst, i) ← fill.loop1 dst n i fuel",
		"pure (i, dst)",
		"def classify (v : Array UInt8) (at_ : UInt32) (fuel : Nat) : Option (Pair) := do",
		"let p ← (if (decide ((v.getD at_.toNat (0 : UInt8)) < (128 : UInt8))) then (do",
		"let p := { p with lo := (1 : UInt32) }",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("extraction lacks %q:\n%s", want, out)
		}
	}
	if strings.Contains(out, "sorry") {
		t.Fatalf("extraction contains sorry:\n%s", out)
	}
}

// Calls are hoisted before the statement that uses them and bound with the
// spans they write; callees precede callers whatever the source order.
func TestExtractionCallsAndOrder(t *testing.T) {
	src := `
main_check: (text: []u8): Bool {
  state: [2]u32
  kind: u32 = next(text, span(&state))
  kind == u32(1) && state[0] > u32(0)
}
next: (text: []u8, state: [*]u32): u32 {
  state[0] = state[0] + u32(1)
  state[0] < len(text) ? u32(1) | u32(0)
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Index(out, "def next ") > strings.Index(out, "def main_check ") {
		t.Fatalf("callee must precede caller:\n%s", out)
	}
	for _, want := range []string{
		"let (r1, state) ← next text state fuel",
		"let kind : UInt32 := r1",
		"pure ((if (decide ((state.getD 0 (0 : UInt32)) < (text.size.toUInt32))) then (1 : UInt32) else (0 : UInt32)), state)",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("extraction lacks %q:\n%s", want, out)
		}
	}
}

// Everything outside the subset is an error, never an approximation.
// Integer-constant matches extract as equality chains, in value and in
// statement position, and the integer conversion rows as Lean's wrapping
// and clamping conversions (the ml subset: an op dispatch on constants,
// u64 index arithmetic narrowed to u32).
func TestExtractionIntegerMatchesAndConversions(t *testing.T) {
	src := `
apply: (op: u32, a: u64, b: u64): u64 {
  op ? {
    | 0 => a + b
    | 1 => a - b
    | _ => u64(0)
  }
}
narrow: (x: u64, y: i32): u32 {
  total: u32 = u32_trunc_u64(x)
  op: u32 = u32(2)
  op ? {
    | 0 => { total = total + u32(1) }
    | 2 => { total = total + u8_saturating_u32(total) }
    | _ => { total = u32(0) }
  }
  total + u32_bits_i32(y) + u32_bits_i32(i32(i8_saturating_i32(y)))
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"(if (op == (0 : UInt32)) then (a + b) else if (op == (1 : UInt32)) then (a - b) else (0 : UInt64))",
		"(x.toUInt32)",
		"let total ← (if (op == (0 : UInt32)) then (do",
		"else if (op == (2 : UInt32)) then (do",
		"(if total > (255 : UInt32) then (255 : UInt8) else total.toUInt8).toUInt32",
		"(y.toUInt32)",
		"(if y > (127 : Int32) then (127 : Int8) else if y < (-128 : Int32) then (-128 : Int8) else y.toInt8)",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("missing %q in:\n%s", want, out)
		}
	}
}

func TestExtractionFailsClosed(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"recursion":      {"f: (n: u32): u32 = n == u32(0) ? u32(0) | f(n - u32(1))", "recursive"},
		"float row":      {"f: (x: u32): u32 = u32_trunc_f32(f32_round_u32(x))", "integer conversions only"},
		"mixed patterns": {"f: (n: u32): u32 = n ? | 0 => u32(1) | k => k", "outside the extracted subset"},
		"template call":  {"Kind: type = Word | Line\nf[T]: (k: T): T = k\ng: (k: Kind): Kind = f[Kind](k)\nh: (): u32 = u32(1)", ""},
		"string":         {"s: (): string = \"x\"", "outside the extracted subset"},
	}
	for name, c := range cases {
		out, err := extract(t, c.src)
		if c.want == "" {
			if err != nil {
				t.Fatalf("%s: %v", name, err)
			}
			if !strings.Contains(out, "def f_Kind (k : Kind)") || strings.Contains(out, "def f (") {
				t.Fatalf("%s: instantiation must be extracted under its mangled name and the template never:\n%s", name, out)
			}
			continue
		}
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", name, err, c.want)
		}
	}
}

// Sum types extract as inductives (generic ones per recorded instantiation
// under the checker's mangled name), variant construction as constructor
// application, matches over variants as Lean matches in value and statement
// position, a value-position arm carrying statements or calls as a bound
// do-block, bitwise operators as their Lean spellings, and a checked
// conversion as the Result it builds.
func TestExtractionSumTypes(t *testing.T) {
	src := `
Option[T]: type = Some: T | None
Result[T, E]: type = Ok: T | Err: E
Overflow: type = | Overflow
Fault: type = Short | Bad: u32
Item: type = struct { value: u64, next: u32 }
size: (value: u64): u32 {
  n: u32 = u32(1)
  rest: u64 = value >> u64(7)
  while rest != u64(0) {
    rest = rest >> u64(7)
    n = n + u32(1)
  }
  n
}
encode: (dst: [*]u8, value: u64): Result[u32, Fault] {
  n: u32 = size(value)
  n > len(dst) ? { .Err(.Bad(n)) } | {
    dst[0] = u8_trunc_u64(value & u64(127)) | u8(128)
    .Ok(n)
  }
}
first: (src: []u8): Option[Item] = len(src) == u32(0) ? .None | .Some(Item { value: u64(src[0]), next: u32(1) })
value_of: (r: Result[u32, Fault]): u32 = r ? | .Ok(n) => n | .Err(.Bad(k)) => k | .Err(_) => u32(0)
count: (src: []u8): u32 {
  total: u32 = u32(0)
  first(src) ? | .Some(item) => { total = item.next ^ u32(3) } | .None => { total = u32(0) }
  total
}
narrow: (n: u32): Result[u8, Overflow] = u8_checked_u32(n)
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"inductive Fault where\n  | Short\n  | Bad (payload : UInt32)\n  deriving Repr, Inhabited, BEq, DecidableEq",
		"inductive Result_u32_Fault where\n  | Ok (payload : UInt32)\n  | Err (payload : Fault)",
		"inductive Option_Item where\n  | Some (payload : Item)\n  | None",
		"structure Item where\n  value : UInt64\n  next : UInt32\n  deriving Repr, Inhabited, BEq, DecidableEq",
		"def encode (dst : Array UInt8) (value : UInt64) (fuel : Nat) : Option (Result_u32_Fault × Array UInt8) := do",
		"let (r2, dst) ← (\n    if (decide (n > (dst.size.toUInt32))) then (do",
		"pure ((Result_u32_Fault.Err (Fault.Bad n)), dst))",
		"let dst := dst.setIfInBounds 0 (((value &&& (127 : UInt64)).toUInt8) ||| (128 : UInt8))",
		"pure ((Result_u32_Fault.Ok n), dst))",
		"let rest : UInt64 := (value >>> (7 : UInt64))",
		"(if ((src.size.toUInt32) == (0 : UInt32)) then Option_Item.None else (Option_Item.Some ({ value := ((src.getD 0 (0 : UInt8)).toUInt64), next := (1 : UInt32) } : Item)))",
		"(match r with | (.Ok n) => n | (.Err (.Bad k)) => k | (.Err _) => (0 : UInt32))",
		"let total ← (match r1 with\n    | (.Some item) => (do\n      let total := (item.next ^^^ (3 : UInt32))\n      pure total)\n    | .None => (do\n      let total := (0 : UInt32)\n      pure total))",
		"(if n > (255 : UInt32) then Result_u8_Overflow.Err Overflow.Overflow else Result_u8_Overflow.Ok n.toUInt8)",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("extraction lacks %q:\n%s", want, out)
		}
	}
	if strings.Contains(out, "inductive Option where") || strings.Contains(out, "inductive Result where") {
		t.Fatalf("templates must never be emitted:\n%s", out)
	}
}

// Top-level constants extract as definitions, array literals as Lean array
// literals, and a view of a constant table is the table's value; a
// writable span of a global fails closed.
func TestExtractionTablesAndGlobals(t *testing.T) {
	src := `
SYMBOLS: [4]u8 = [4]u8{ 48, 49, 50, 51 }
LIMIT: u32 = 3
digit: (n: u32, upper: Bool): u8 {
  table: []u8 = upper ? view(&SYMBOLS) | view(&SYMBOLS)
  n < LIMIT ? table[n] | SYMBOLS[0]
}
pair: (a: u32): [2]u32 = [2]u32{ a, a + u32(1) }
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"def SYMBOLS : Array UInt8 := (#[(48 : UInt8), (49 : UInt8), (50 : UInt8), (51 : UInt8)] : Array UInt8)",
		"def LIMIT : UInt32 := (3 : UInt32)",
		"let table : Array UInt8 := (if upper then SYMBOLS else SYMBOLS)",
		"pure (if (decide (n < LIMIT)) then (table.getD n.toNat (0 : UInt8)) else (SYMBOLS.getD 0 (0 : UInt8)))",
		"pure (#[a, (a + (1 : UInt32))] : Array UInt32)",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("extraction lacks %q:\n%s", want, out)
		}
	}
	if strings.Index(out, "def SYMBOLS") > strings.Index(out, "def digit") {
		t.Fatalf("constants must precede the functions that read them:\n%s", out)
	}
	_, err = extract(t, "TABLE: [2]u8 = [2]u8{ 1, 2 }\nzap: (): () { s: [*]u8 = span(&TABLE)\n  s[0] = u8(0) }")
	if err == nil || !strings.Contains(err.Error(), "span of the global") {
		t.Fatalf("span of a global must fail closed, got %v", err)
	}
}

// subslice(v, start, n) is the window of n elements from start as
// Array.extract; Oak traps past the end, the extraction clamps
// (docs/spec/95-extraction.md section 3).
func TestExtractionSubslice(t *testing.T) {
	src := `
window_sum: (src: []u8, at: u32): u32 {
  win: []u8 = subslice(src, at, u32(4))
  total: u32 = 0
  i: u32 = 0
  while i < len(win) {
    total = total + u32(win[i])
    i = i + u32(1)
  }
  total
}
`
	out, err := extract(t, src)
	if err != nil {
		t.Fatal(err)
	}
	want := "let win : Array UInt8 := (src.extract at_.toNat (at_.toNat + (4 : UInt32).toNat))"
	if !strings.Contains(out, want) {
		t.Fatalf("extraction lacks %q:\n%s", want, out)
	}
}
