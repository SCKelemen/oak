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
		"recursion": {"f: (n: u32): u32 = n == u32(0) ? u32(0) | f(n - u32(1))", "recursive"},
		"checked":   {"Overflow: type = | Overflow\nResult[T, E]: type = Ok: T | Err: E\nf: (n: u32): Result[u8, Overflow] = u8_checked_u32(n)", "only record types are extracted"},
		"float row": {"f: (x: u32): u32 = u32_trunc_f32(f32_round_u32(x))", "integer conversions only"},
		"mixed patterns": {"f: (n: u32): u32 = n ? | 0 => u32(1) | k => k", "outside the extracted subset"},
		"adt match": {"Kind: type = Word | Line\nclassify: (k: Kind): u32 = k ? | .Word => u32(2) | .Line => u32(1)", "only record types are extracted"},
		"string":    {"s: (): string = \"x\"", "outside the extracted subset"},
	}
	for name, c := range cases {
		_, err := extract(t, c.src)
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", name, err, c.want)
		}
	}
}
