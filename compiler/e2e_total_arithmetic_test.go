package compiler

import (
	"strings"
	"testing"
)

// Fixed-width arithmetic is total with two's-complement semantics
// (docs/spec/20-types.md §11.1, docs/spec/90-backend.md §7): every width
// wraps mod 2^N at the expression, not only at a store, and no C promotion,
// signed overflow, or implementation-defined conversion is involved. Verified
// in running machine code, for the bare-literal and cast spellings alike.
func TestE2EFixedWidthArithmeticWraps(t *testing.T) {
	code, abnormal := buildAndRun(t, "total_arith", `
counter: u8 = 250
limit: u16 = 65535
product: u16 = 300 * 200

step: (n: i32): i32 {
  n + -1
}
main: (): i32 {
  full: u8 = 255
  assert(full + 1 == 0)
  assert(full + u8(1) == 0)
  half: u8 = 127
  assert(half * 2 + 2 == 0)
  assert(half * 3 == 125)
  zero: u8 = 0
  assert(zero - 1 == 255)
  assert(counter + 10 == 4)

  wide: u16 = 65535
  assert(wide * wide == 1)
  assert(limit + 1 == 0)
  assert(product == 60000)

  top: u32 = 4294967295
  assert(top + 1 == 0)
  assert(top * top == 1)
  assert(0 - top == 1)

  low: i32 = -2147483648
  assert(step(low) == 2147483647)
  assert(low - 1 == 2147483647)
  assert(low * 2 == 0)
  assert(low / -1 == low)
  assert(low % -1 == 0)
  high: i32 = 2147483647
  assert(high + 1 == low)
  assert(high * 2 == -2)
  assert(-7 / 2 == -3)
  assert(-7 % 2 == -1)
  seven: i32 = -7
  assert(seven / 2 == -3)
  assert(seven % 2 == -1)

  tiny: i8 = 127
  assert(tiny + 1 == -128)
  narrow: i8 = -128
  assert(narrow / -1 == narrow)
  assert(narrow - 1 == 127)

  big: i64 = 9223372036854775807
  assert(big + 1 == -9223372036854775807 - 1)
  least: i64 = -9223372036854775807 - 1
  assert(least / -1 == least)

  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Division by zero traps for every width (fail-stop, the same doctrine as
// bounds checks and shifts), instead of being undefined.
func TestE2EDivisionByZeroTraps(t *testing.T) {
	for _, c := range []struct{ name, typ, op string }{
		{"div_u8", "u8", "/"}, {"rem_u32", "u32", "%"}, {"div_i32", "i32", "/"}, {"rem_i64", "i64", "%"},
	} {
		t.Run(c.name, func(t *testing.T) {
			code, abnormal := buildAndRun(t, c.name, `
divisor: `+c.typ+` = 0
main: (): i32 {
  n: `+c.typ+` = 7
  r: `+c.typ+` = n `+c.op+` divisor
  r == 7 ? { 1 } | { 42 }
}
`)
			if !abnormal {
				t.Fatalf("%s: exit %d, want a trap", c.name, code)
			}
		})
	}
}

// Constant contexts keep plain C arithmetic: file-scope initializers and
// static_assert must remain integer constant expressions, and literal-only
// operands never need a helper.
func TestTotalArithmeticKeepsConstantContexts(t *testing.T) {
	output, err := New().WithSource("consts.oak", `
base: u32 = 8 + 2
ratio: i32 = 100 / 7
static_assert(size_of[u32]() * 2 == 8)

scaled: (n: u32): u32 {
  n * 2 + 1
}
main: (): i32 {
  static_assert(size_of[u16]() + 2 == 4)
  assert(scaled(base) == 21)
  assert(ratio == 14)
  42
}
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"static u32 base = ( 8 + 2 )", "static i32 ratio = ( 100 / 7 )", "oak_add_u32( oak_mul_u32( n, 2 ), 1 )"} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "oak_static_assert_0[ ( ( oak_") || strings.Contains(output, "char[ ( ( oak_") {
		t.Fatalf("static_assert used an arithmetic helper:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "consts_run", `
base: u32 = 8 + 2
scaled: (n: u32): u32 {
  n * 2 + 1
}
main: (): i32 {
  static_assert(size_of[u16]() + 2 == 4)
  assert(scaled(base) == 21)
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
