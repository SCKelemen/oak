package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A frame-held record local's sixty-four-element array field, written in
// a loop, is a span memory of the local on both sides (the backend names
// the field's frame object, asm/return_slot.go, declareSpanFields): the
// prover's add_carry builds its Bits in the frame and returns it inside a
// Sum, and pop_count passes a frame-held Bits to a callee.
const nativeFrameSpanProgram = `Bits: type = struct { at: [64]u32 }
Sum: type = struct { bits: Bits, carry: u32 }

carry_add: (a: Bits, b: Bits, w: u32): Sum {
  out: Bits
  c: u32 = 0
  i: u32 = 0
  while i < w {
    s: u32 = a.at[i] + b.at[i] + c
    out.at[i] = s & u32(1)
    c = s >> u32(1)
    i = i + u32(1)
  }
  Sum { bits: out, carry: c }
}

weight: (v: Bits, w: u32): u32 {
  n: u32 = 0
  i: u32 = 0
  while i < w {
    n = n + v.at[i]
    i = i + u32(1)
  }
  n
}

ones_of: (a: Bits, w: u32): u32 {
  one: Bits
  i: u32 = 0
  while i < w {
    one.at[i] = a.at[i] & u32(1)
    i = i + u32(1)
  }
  weight(one, w)
}

main: (): i32 {
  x: Bits
  y: Bits
  k: u32 = 0
  while k < u32(64) {
    x.at[k] = k & u32(1)
    y.at[k] = u32(1)
    k = k + u32(1)
  }
  s: Sum = carry_add(x, y, u32(64))
  i32_bits_u32(s.bits.at[0] + s.bits.at[1] + s.carry + ones_of(x, u32(64)) + u32(8))
}
`

func TestE2ENativeFrameSpan(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("frame_span.oak", nativeFrameSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "frame_span", comp)
	joined := strings.Join(infos, "\n")
	// x = 0,1,0,1,…; y = 1,…: bit 0: 0+1+0 = 1 (carry 0); bit 1: 1+1+0 = 2 → 0, carry 1;
	// the chain ends with carry 1; ones_of(x) = 32: 1 + 0 + 1 + 32 + 8 = 42.
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, want := range []string{
		"asm unit carry_add: proven equal to its Oak body",
		"asm unit ones_of: proven equal to its Oak body",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("want %q in the diagnostics:\n%s", want, joined)
		}
	}
}
