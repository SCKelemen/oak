package compiler

// A u16 or u8 loop counter (the OS pilot's `i: u16` over max_pages in
// reset) lives in a 32-bit general register, zero-extended after each step
// (`and #0xFFFF`); the loop coupling pairs the narrow Oak variable with the
// register through a widening image (docs/spec/94-assembler.md §8), where
// before no register was "an affine image of the loop variable i" and the
// unit was evidence, not proof.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeNarrowCounterProgram = `count16: (n: u16): u32 {
  i: u16 = u16(0)
  acc: u32 = u32(0)
  while i < n {
    acc = acc + u32(i)
    i = i + u16(1)
  }
  acc
}

count8: (n: u8): u32 {
  i: u8 = u8(0)
  acc: u32 = u32(0)
  while i < n {
    acc = acc + u32(i) * u32(3)
    i = i + u8(1)
  }
  acc
}

fill16: (s: [*]u32, n: u16): u16 {
  i: u16 = u16(0)
  while i < n && u32(i) < len(s) {
    s[u32(i)] = u32(i) * u32(2)
    i = i + u16(1)
  }
  i
}

main: (): i32 {
  buf: [8]u32
  k: u16 = fill16(span(&buf), u16(6))
  (count16(u16(5)) == u32(10) && count8(u8(4)) == u32(18) && k == u16(6) && buf[5] == u32(10)) ? 42 | 1
}
`

func TestE2ENativeNarrowCountersProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("narrow.oak", nativeNarrowCounterProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "narrow_counters", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"count16", "count8", "fill16"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level — data-dependent loop coupled inductively (i↔") {
			t.Errorf("%s's narrow counter must couple with its register; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit fill16: proven") || !strings.Contains(joined, "and the span memory it writes (s)") {
		t.Errorf("fill16's stores must be decided; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "narrow_counters_c", New().WithSource("narrow.oak", nativeNarrowCounterProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
