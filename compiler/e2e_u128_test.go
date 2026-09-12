package compiler

import (
	"strings"
	"testing"
)

// u128 (docs/spec/20-types.md section 11): a 128-bit unsigned fixed-width
// integer with the same total semantics as the other widths — wrapping
// arithmetic, checked shifts, unsigned ordering, the trunc/saturating/
// checked narrowings down to u64 — in both realizations. The layout
// assertions run only compiled: 16 bytes at 16-byte alignment, ratified
// by the C compiler.
const u128Body = `package main
import(std)
import("wide")
Header: type = struct { checksum: u128, size: u32, id: u128 }
two_to_64: (): u128 = u128(1) << u128(64)
compute: (): i32 {
  one: u128 = u128(1)
  two64: u128 = two_to_64()
  max: u128 = u128(0) - one
  assert(max + one == u128(0))
  assert(-one == max)
  assert(two64 > u128(18446744073709551615))
  assert(u128(18446744073709551615) + one == two64)
  assert(two64 * u128(3) >> u128(64) == u128(3))
  assert((two64 + u128(7)) / two64 == one)
  assert((two64 + u128(7)) % two64 == u128(7))
  assert(two64 * two64 == u128(0))
  assert((max ^ u128(255)) == max - u128(255))
  assert((two64 | one) & one == one)
  assert(^u128(0) == max)
  assert(wide.high(two64 * u128(5)) == u64(5))
  assert(wide.low(two64 + u128(9)) == u64(9))
  assert(wide.pack(u64(5), u64(9)) == two64 * u128(5) + u128(9))
  assert(u64_trunc_u128(two64 + u128(3)) == u64(3))
  assert(u64_saturating_u128(two64) == u64(18446744073709551615))
  assert(u64_saturating_u128(u128(77)) == u64(77))
  assert_eq(u64_trunc_u128(max), u64(18446744073709551615))
  assert_eq(two64 - one, u128(18446744073709551615))
  assert(u8_trunc_u128(two64 + u128(258)) == u8(2))
  too_wide: Bool = u64_checked_u128(two64) ? | .Ok(_) => false | .Err(_) => true
  assert(too_wide)
  fits: Bool = u64_checked_u128(u128(42)) ? | .Ok(v) => v == u64(42) | .Err(_) => false
  assert(fits)
  widened: u128 = u128(u32(7))
  assert(widened * u128(6) == u128(42))
  h: Header = Header { checksum: max, size: u32(1), id: two64 }
  h.checksum == max && h.id == two64 && h.size == u32(1) ? 42 | 1
}
`

func u128Module(t *testing.T, program string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/u128_check\noak 0.1.0\n",
		"main.oak": program,
	})
}

func TestE2EU128Compiled(t *testing.T) {
	src := u128Body + `
main: (): i32 {
  static_assert(size_of[u128]() == u32(16))
  static_assert(align_of[u128]() == u32(16))
  static_assert(size_of[Header]() == u32(48))
  static_assert(offset_of[Header](id) == u32(32))
  compute()
}
`
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(u128Module(t, src)))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EU128Interpreted(t *testing.T) {
	if got := interpretModule(t, u128Module(t, u128Body+"main: (): i32 = compute()\n")); got != 42 {
		t.Fatalf("interpreter: got %d, want 42", got)
	}
}

// A shift count reaching the width traps in the compiled program, as at
// every other width (docs/spec/10-syntax.md section 3b).
func TestE2EU128ShiftTraps(t *testing.T) {
	src := `
shift: (n: u128): u128 = u128(1) << n
main: (): i32 = u64_trunc_u128(shift(u128(128))) == u64(0) ? 1 | 2
`
	_, abnormal := buildAndRun(t, "u128_shift", src)
	if !abnormal {
		t.Fatal("a shift by 128 did not trap")
	}
}

// The checker keeps u128 inside the integer rules: no implicit narrowing,
// no signed sources, no constant shift at the width, no checked family,
// and no i128.
func TestU128Rejections(t *testing.T) {
	cases := map[string]struct{ src, want string }{
		"implicit narrowing": {"main: (): i32 { x: u64 = u128(1)\n 0 }", "u128"},
		"widening back":      {"main: (): i32 { x: u64 = u64(u128(1))\n 0 }", "cannot widen u128 to u64"},
		"signed source":      {"main: (): i32 { x: u128 = u128(i32(1))\n 0 }", "cannot widen i32 to u128"},
		"signed target":      {"main: (): i32 { x: i64 = i64(u128(1))\n 0 }", "cannot widen u128 to i64"},
		"constant shift":     {"main: (): i32 { x: u128 = u128(1) << 128\n 0 }", "shift count 128 out of range for u128 (width 128)"},
		"no i128":            {"main: (): i32 { x: i128 = i128(1)\n 0 }", "i128"},
		"no checked family":  {"import(std)\nmain: (): i32 { r: Result[u128, Overflow] = u128_checked_add(u128(1), u128(2))\n 0 }", "u128_checked_add"},
		"signed operand":     {"main: (): i32 { y: i64 = i64(2)\n x: u128 = u128(1) + y\n 0 }", "i64"},
		"bits reinterpret":   {"main: (): i32 { x: u128 = u128_bits_i64(i64(1))\n 0 }", "u128_bits_i64"},
	}
	for name, c := range cases {
		_, err := New().WithSource("bad.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: want %q, got %v", name, c.want, err)
		}
	}
}

// Lean has no 128-bit machine integer: extraction of a u128 function is
// refused, not narrowed (docs/spec/95-extraction.md).
func TestU128OutsideLeanSubset(t *testing.T) {
	src := "bump: (x: u128): u128 = x + u128(1)\nmain: (): i32 = 0\n"
	_, err := New().WithSource("wide.oak", src).EmitLeanRoots("Oak.Wide", []string{"bump"}).Get()
	if err == nil || !strings.Contains(err.Error(), "outside the extracted subset") {
		t.Fatalf("want an extraction refusal, got %v", err)
	}
}
