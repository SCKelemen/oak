package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record built in the result area whose array field has sixty-four
// elements written in a loop: the field is a span memory of the local on
// both sides (asm/return_slot.go, declareReturnSlot, frameSpanAccess),
// so the loop's stores couple write by write where sixty-four leaves,
// each a conditional over the index per iteration, exceeded the
// coupling's term budget (the prover's Bits family).
const nativeResultSpanProgram = `Bits: type = struct { at: [64]u32 }

shift_up: (a: Bits, w: u32): Bits {
  out: Bits
  i: u32 = 0
  while i < w {
    out.at[i] = a.at[i] + i
    i = i + u32(1)
  }
  out
}

merge: (a: Bits, b: Bits, w: u32): Bits {
  out: Bits
  i: u32 = 0
  while i < w {
    out.at[i] = (a.at[i] & b.at[i]) | (i & u32(1))
    i = i + u32(1)
  }
  out
}

main: (): i32 {
  x: Bits
  y: Bits
  k: u32 = 0
  while k < u32(64) {
    x.at[k] = k
    y.at[k] = u32(64) - k
    k = k + u32(1)
  }
  s: Bits = shift_up(x, u32(64))
  m: Bits = merge(x, y, u32(64))
  i32_bits_u32(s.at[20] + m.at[7] + m.at[8] - u32(3))
}
`

func TestE2ENativeResultSpan(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("result_span.oak", nativeResultSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "result_span", comp)
	joined := strings.Join(infos, "\n")
	// s.at[20] = 40; m.at[7] = (7 & 57) | 1 = 1; m.at[8] = (8 & 56) | 0 = 8; 40 + 1 + 8 - 3 = 46... adjusted below.
	if abnormal {
		t.Fatalf("native: abnormal exit %d\n%s", code, joined)
	}
	if code != 46 {
		t.Fatalf("native: exit = %d, want 46\n%s", code, joined)
	}
	for _, want := range []string{
		"asm unit shift_up: proven equal to its Oak body",
		"asm unit merge: proven equal to its Oak body",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("want %q in the diagnostics:\n%s", want, joined)
		}
	}
}
