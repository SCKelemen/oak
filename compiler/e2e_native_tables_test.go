package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Constant tables through the verifier (docs/spec/94-assembler.md §9): a
// body reading a top-level constant array is proven — the read is a lookup
// over the table on both sides, folded at a constant index — where it was
// trusted for the `adrl` alone. The C backend's realization is the oracle.
const nativeTablesProgram = `
DIGITS: [16]u8 = [u8(48), u8(49), u8(50), u8(51), u8(52), u8(53), u8(54), u8(55), u8(56), u8(57), u8(97), u8(98), u8(99), u8(100), u8(101), u8(102)]
WEIGHTS: [4]u16 = [u16(1), u16(10), u16(100), u16(1000)]

hex_digit: (v: u32) -> u8 = DIGITS[v & u32(15)]

// A constant index and len.
zero_digit: (): u8 = DIGITS[u32(0)]
digit_count: (): u32 = u32(len(DIGITS))

// A wider element, and a table read inside a conditional.
weight: (i: u32, wide: Bool) -> u32 = wide ? u32(WEIGHTS[i & u32(3)]) | u32(DIGITS[i & u32(15)])

main: (): i32 {
  assert(hex_digit(u32(10)) == u8(97))
  assert(hex_digit(u32(0x1F)) == u8(102))
  assert(zero_digit() == u8(48))
  assert(digit_count() == u32(16))
  assert(weight(u32(3), true) == u32(1000))
  assert(weight(u32(3), false) == u32(51))
  42
}
`

func TestE2ENativeTables(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("tables.oak", nativeTablesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_tables", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native tables: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"hex_digit", "zero_digit", "digit_count", "weight"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal") {
			t.Errorf("%s reads a constant table and must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	if strings.Contains(joined, "instruction adrl") {
		t.Errorf("a table read fell outside the subset:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_tables_c", New().WithSource("tables.oak", nativeTablesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
