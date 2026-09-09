package compiler

import "testing"

// The interpreter wraps fixed-width arithmetic and negation exactly as the
// compiled backend does (docs/spec/20-types.md §11.1): the same program,
// folding every wrap boundary into one checksum, must produce the same value
// through both realizations.
func TestDifferentialIntegerWrap(t *testing.T) {
	src := `
step: (n: i32): i32 {
  n + -1
}
main: (): i32 {
  full: u8 = 255
  half: u8 = 127
  zero: u8 = 0
  wide: u16 = 65535
  top: u32 = 4294967295
  low: i32 = -2147483648
  high: i32 = 2147483647
  tiny: i8 = -128
  seven: i32 = -7

  sum: i32 = 0
  sum = sum + i32(full + 1)
  sum = sum + i32(half * 2 + 2)
  sum = sum + i32(zero - 1)
  sum = sum + i32(-full)
  sum = sum + i32(wide * wide)
  sum = sum + i32(u16(wide + 1))
  sum = sum + i32(u16_trunc_u32(top + 1))
  sum = sum + i32(u16_trunc_u32(0 - top))
  sum = sum + i32(u16_trunc_u32(top * top))
  sum = sum + step(low) % 1000
  sum = sum + (low - 1) % 1000
  sum = sum + low * 2
  sum = sum + (low / -1) % 1000
  sum = sum + low % -1
  sum = sum + (high + 1) % 1000
  sum = sum + high * 2
  sum = sum + seven / 2
  sum = sum + seven % 2
  sum = sum + i32(tiny + -1)
  sum = sum + i32(tiny / -1)
  sum = sum + i32(-tiny)
  sum = sum + i32(-low % 1000)
  result: i32 = (sum % 100 + 100) % 100
  result
}
`
	interpreted := interpretChecked(t, src)
	compiled := buildAndReturn(t, "integer_wrap", src)
	if interpreted != compiled {
		t.Fatalf("interpreter %d, compiled %d", interpreted, compiled)
	}
	t.Logf("wrap checksum agrees: %d", interpreted)
}

// buildAndReturn runs the compiled program and decodes main's result from
// the process exit status, which the C entry point returns directly; the
// program keeps that result inside 0..99.
func buildAndReturn(t *testing.T, name, src string) int64 {
	t.Helper()
	stdout, code, abnormal := buildAndRunOutput(t, name, `
`+src+`
`)
	if abnormal {
		t.Fatalf("compiled program trapped: %q", stdout)
	}
	return int64(code)
}
