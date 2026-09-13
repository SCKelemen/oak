package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Large record strides (the OS pilot's N2: a 409 600-byte regime). A span
// element of a record wider than 65 536 bytes is addressed by `umaddl`
// with the stride built as movz then movk; the checker keeps the stride
// constant through the movk, so the element region is derived and the
// field loads and stores inside it are admitted. The functions lower
// natively and agree with the C backend.
const nativeStrideProgram = `
Regime: type = struct { table: [70000]u8, count: u32, mark: u64 }

mark_regime: (regimes: [*]Regime, i: u32, value: u64): u64 {
  i < len(regimes) ? {
    regimes[i].count = regimes[i].count + u32(1)
    regimes[i].mark = value + u64(regimes[i].count)
    regimes[i].mark
  } | { u64(0) }
}

read_count: (regimes: []Regime, i: u32): u32 {
  i < len(regimes) ? { regimes[i].count } | { u32(0) }
}

main: (): i32 {
  regimes: [3]Regime
  a: u64 = mark_regime(span(&regimes), u32(2), u64(100))
  b: u64 = mark_regime(span(&regimes), u32(2), u64(200))
  c: u32 = read_count(view(&regimes), u32(2)) + read_count(view(&regimes), u32(0))
  // 101 + 202 + 2 = 305; the exit code carries the low byte, 49.
  i32_bits_u32(u32_trunc_u64(a + b) + c)
}
`

func TestE2ENativeLargeStrides(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("stride.oak", nativeStrideProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_stride", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 305%256 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want %d\n%s", code, abnormal, 305%256, joined)
	}
	for _, fn := range []string{"mark_regime", "read_count"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively over a 70 KiB stride; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_stride_c", New().WithSource("stride.oak", nativeStrideProgram)); abnormal || code != 305%256 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want %d", code, abnormal, 305%256)
	}
}
