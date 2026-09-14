package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Unsigned division and remainder by a constant power of two lower to a
// shift and a mask (nativegen, docs/spec/94-assembler.md §9), as the
// Oak-side lowering already spelled them: the bodies are proven at the bit
// level, where a udiv (an uninterpreted operation) left them witnessed.
// Any other divisor keeps the zero check and the udiv.
const nativePow2DivProgram = `
half: (x: u32): u32 = x / u32(2)

low3: (x: u64): u64 = x % u64(8)

mid: (lo: u32, hi: u32): u32 = lo + (hi - lo) / u32(2)

pages: (n: u32): u32 = n / u32(512)

by_ten: (x: u32): u32 = x / u32(10)

main: (): i32 {
  // 21 + 5 + 30 + 2 + 4 = 62
  i32_bits_u32(half(u32(43)) + u32_trunc_u64(low3(u64(0xFFFD))) + mid(u32(20), u32(41)) + pages(u32(1500)) + by_ten(u32(47)))
}
`

func TestE2ENativePow2Division(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("pow2_div.oak", nativePow2DivProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_pow2_div", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 62 {
		t.Fatalf("native pow2 division: exit = (%d, abnormal=%v), want 62\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"half", "low3", "mid", "pages"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body") {
			t.Errorf("%s must be proven (a shift or a mask, not an uninterpreted quotient); diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit by_ten:") {
		t.Errorf("by_ten must still be lowered (udiv behind its zero check); diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_pow2_div_c", New().WithSource("pow2_div.oak", nativePow2DivProgram)); abnormal || code != 62 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 62", code, abnormal)
	}
}
