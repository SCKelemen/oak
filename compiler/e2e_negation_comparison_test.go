package compiler

import (
	"strings"
	"testing"
)

// Unary minus is total in the operand's own width: two's-complement
// negation mod 2^N for unsigned and signed alike, so `-x` never changes
// signedness and `-MIN` wraps to MIN instead of being undefined.
func TestE2ENegationIsTotal(t *testing.T) {
	code, abnormal := buildAndRun(t, "negation", `
flip: (n: u32): u32 {
  -n
}
main: (): i32 {
  full: u8 = 255
  assert(-full == 1)
  one: u8 = 1
  assert(-one == 255)
  zero: u32 = 0
  assert(-zero == 0)
  assert(flip(1) == 4294967295)
  assert(flip(flip(7)) == 7)

  low: i32 = -2147483648
  assert(-low == low)
  seven: i32 = 7
  assert(-seven == -7)
  assert(-(-seven) == 7)
  tiny: i8 = -128
  assert(-tiny == tiny)
  least: i64 = -9223372036854775807 - 1
  assert(-least == least)
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Comparisons follow the arithmetic rule: one signedness, widths promote.
func TestComparisonsRequireOneSignedness(t *testing.T) {
	rejected := []struct{ name, src string }{
		{"less", "f: (a: u32, b: i32): Bool { a < b }"},
		{"greater-equal", "f: (a: i8, b: u8): Bool { a >= b }"},
		{"equal", "f: (a: u64, b: i64): Bool { a == b }"},
		{"not-equal", "f: (a: i32, b: u8): Bool { a != b }"},
	}
	for _, c := range rejected {
		t.Run(c.name, func(t *testing.T) {
			_, err := New().WithSource(c.name+".oak", c.src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), "cannot mix signed and unsigned types") {
				t.Fatalf("%s: expected a signedness error, got %v", c.name, err)
			}
		})
	}
	code, abnormal := buildAndRun(t, "comparisons", `
main: (): i32 {
  small: u8 = 200
  wide: u32 = 300
  assert(small < wide)
  assert(wide > small)
  assert(small != wide)
  neg: i8 = -5
  big: i64 = 1000000
  assert(neg < big)
  assert(big >= neg)
  assert(neg == -5)
  assert(wide == 300)
  assert(2 < wide)
  42
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
