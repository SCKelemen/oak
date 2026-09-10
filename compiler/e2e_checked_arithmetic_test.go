package compiler

import (
	"strings"
	"testing"
)

// Checked and saturating arithmetic (docs/spec/20-types.md section 11.1a):
// `{type}_checked_{add|sub|mul}` returns Result[type, Overflow] and
// `{type}_saturating_{add|sub|mul}` clamps, at every boundary the wrapping
// operators cross silently. The interpreter computes the exact result in
// arbitrary precision, the C helpers use the overflow builtins; both
// realizations must agree.
const checkedArithmeticProgram = `
Result[T, E]: type = Ok: T | Err: E
Overflow: type = | Overflow
ok_u8: (r: Result[u8, Overflow], want: u8): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
ok_u32: (r: Result[u32, Overflow], want: u32): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
ok_u64: (r: Result[u64, Overflow], want: u64): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
ok_i8: (r: Result[i8, Overflow], want: i8): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
ok_i32: (r: Result[i32, Overflow], want: i32): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
ok_i64: (r: Result[i64, Overflow], want: i64): Bool = r ? | .Ok(v) => v == want | .Err(e) => false
err_u8: (r: Result[u8, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
err_u32: (r: Result[u32, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
err_u64: (r: Result[u64, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
err_i8: (r: Result[i8, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
err_i32: (r: Result[i32, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
err_i64: (r: Result[i64, Overflow]): Bool = r ? | .Ok(v) => false | .Err(e) => true
main: (): i32 {
  // u8: the wrap the operators would take silently
  full: u8 = 255
  assert(full + 1 == 0)
  assert(ok_u8(u8_checked_add(full, 0), 255))
  assert(err_u8(u8_checked_add(full, 1)))
  assert(ok_u8(u8_checked_sub(u8(3), u8(3)), 0))
  assert(err_u8(u8_checked_sub(u8(3), u8(4))))
  assert(ok_u8(u8_checked_mul(u8(15), u8(17)), 255))
  assert(err_u8(u8_checked_mul(u8(16), u8(16))))
  assert(u8_saturating_add(full, 9) == 255)
  assert(u8_saturating_sub(u8(3), u8(4)) == 0)
  assert(u8_saturating_mul(u8(16), u8(16)) == 255)
  assert(u8_saturating_mul(u8(15), u8(17)) == 255)
  // u32: offsets and lengths
  top: u32 = 4294967295
  assert(ok_u32(u32_checked_add(top, 0), top))
  assert(err_u32(u32_checked_add(top, 1)))
  assert(ok_u32(u32_checked_mul(u32(65535), u32(65537)), top))
  assert(err_u32(u32_checked_mul(u32(65536), u32(65536))))
  assert(u32_saturating_add(top, top) == top)
  assert(u32_saturating_sub(u32(1), u32(2)) == 0)
  assert(u32_saturating_mul(u32(65536), u32(65536)) == top)
  // u64: sequence numbers past 2^63
  big: u64 = 18446744073709551615
  half: u64 = 9223372036854775808
  assert(ok_u64(u64_checked_add(half, half - 1), big))
  assert(err_u64(u64_checked_add(half, half)))
  assert(ok_u64(u64_checked_sub(big, half), half - 1))
  assert(err_u64(u64_checked_sub(half - 1, half)))
  assert(ok_u64(u64_checked_mul(u64(4294967295), u64(4294967297)), big))
  assert(err_u64(u64_checked_mul(u64(4294967296), u64(4294967296))))
  assert(u64_saturating_add(big, 1) == big)
  assert(u64_saturating_sub(u64(0), u64(1)) == 0)
  assert(u64_saturating_mul(half, 2) == big)
  // i8: both ends, and the MIN * -1 corner
  assert(ok_i8(i8_checked_add(i8(127), i8(-128)), -1))
  assert(err_i8(i8_checked_add(i8(127), i8(1))))
  assert(err_i8(i8_checked_sub(i8(-128), i8(1))))
  assert(ok_i8(i8_checked_sub(i8(-128), i8(-1)), -127))
  assert(err_i8(i8_checked_mul(i8(-128), i8(-1))))
  assert(ok_i8(i8_checked_mul(i8(-64), i8(2)), -128))
  assert(i8_saturating_add(i8(127), i8(1)) == 127)
  assert(i8_saturating_add(i8(-128), i8(-1)) == -128)
  assert(i8_saturating_sub(i8(-128), i8(1)) == -128)
  assert(i8_saturating_sub(i8(127), i8(-1)) == 127)
  assert(i8_saturating_mul(i8(-128), i8(-1)) == 127)
  assert(i8_saturating_mul(i8(-128), i8(2)) == -128)
  assert(i8_saturating_mul(i8(64), i8(2)) == 127)
  // i32 and i64 at their limits
  imax: i32 = 2147483647
  imin: i32 = -2147483648
  assert(ok_i32(i32_checked_add(imax, -1), 2147483646))
  assert(err_i32(i32_checked_add(imax, 1)))
  assert(err_i32(i32_checked_sub(imin, 1)))
  assert(err_i32(i32_checked_mul(imin, -1)))
  assert(ok_i32(i32_checked_mul(i32(-46341), i32(46340)), -2147441940))
  assert(i32_saturating_sub(imin, 1) == imin)
  assert(i32_saturating_mul(imin, -1) == imax)
  lmax: i64 = 9223372036854775807
  lmin: i64 = -9223372036854775807 - 1
  assert(ok_i64(i64_checked_add(lmax, 0), lmax))
  assert(err_i64(i64_checked_add(lmax, 1)))
  assert(err_i64(i64_checked_sub(lmin, 1)))
  assert(ok_i64(i64_checked_sub(lmin, -1), lmin + 1))
  assert(err_i64(i64_checked_mul(lmin, -1)))
  assert(ok_i64(i64_checked_mul(i64(3037000499), i64(3037000499)), 9223372030926249001))
  assert(err_i64(i64_checked_mul(i64(3037000500), i64(3037000500))))
  assert(i64_saturating_add(lmax, lmax) == lmax)
  assert(i64_saturating_add(lmin, lmin) == lmin)
  assert(i64_saturating_mul(lmin, -1) == lmax)
  assert(i64_saturating_mul(lmin, 2) == lmin)
  42
}
`

func TestE2ECheckedArithmetic(t *testing.T) {
	output, err := New().WithSource("checked.oak", checkedArithmeticProgram).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"__builtin_add_overflow(a, b, &r)",
		"static inline oak_Result_u64_Overflow oak_arith_u64_checked_mul( u64 a, u64 b )",
		"static inline i8 oak_arith_i8_saturating_mul( i8 a, i8 b )",
		"return ((a < 0) == (b < 0)) ? (i8)127 : (i8)(-127 - 1);",
	} {
		if !strings.Contains(output, want) {
			t.Fatalf("generated C lacks %q:\n%s", want, output)
		}
	}
	if strings.Contains(output, "OAK_UNSUPPORTED") || strings.Contains(output, "OAK_CHECKED_ARITHMETIC_NEEDS") {
		t.Fatalf("generated C fails closed somewhere:\n%s", output)
	}
	code, abnormal := buildAndRun(t, "checked", checkedArithmeticProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if interpreted := interpretChecked(t, checkedArithmeticProgram); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// The grammar is one width per call: mixed widths, a float type, a wrong
// argument count, and a checked form without the Result and Overflow
// declarations are rejected before emission.
func TestCheckedArithmeticRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"mixed widths", "main: (): i32 {\n  a: u32 = 1\n  b: u8 = 2\n  c: u32 = u32_saturating_add(a, b)\n  0\n}", "expects operand 2 of type u32"},
		{"one argument", "main: (): i32 {\n  a: u32 = 1\n  c: u32 = u32_saturating_add(a)\n  0\n}", "expects 2 arguments"},
		{"float type", "main: (): i32 {\n  a: f32 = 1.0\n  c: f32 = f32_saturating_add(a, a)\n  0\n}", "f32_saturating_add"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
	// checked without Result/Overflow: the backend fails closed rather
	// than emitting a call to nothing.
	output, err := New().WithSource("noresult.oak", "main: (): i32 {\n  a: u32 = 1\n  r := u32_checked_add(a, a)\n  0\n}").EmitC().Get()
	if err == nil && !strings.Contains(output, "OAK_CHECKED_ARITHMETIC_NEEDS_RESULT_AND_OVERFLOW") {
		t.Fatalf("checked arithmetic without Result/Overflow must fail closed:\n%s", output)
	}
}
