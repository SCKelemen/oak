package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Memory effects through span parameters are verified (docs/spec/94-assembler.md
// §9, twenty-eighth increment): a unit function that stores through a
// span is proven in the span memory it writes, a function with a result
// and stores in both, a read after a write sees the write, a conditional
// store meets the entry memory on the other arm; a store inside a
// data-dependent loop stays trusted with the reason. The C backend's
// realization is the oracle for the values.
const nativeSpanEffectsProgram = `
put: (v: [*]u32, i: u32, x: u32) -> () {
  v[i] = x
}

put3: (v: [*]u32, at: u32, a: u32, b: u32) -> () {
  v[at] = a
  v[at + u32(1)] = b
  v[at + u32(2)] = a ^ b
}

bump: (v: [*]u32, i: u32) -> u32 {
  v[i] = v[i] + u32(1)
  v[i] * u32(2)
}

set_flag: (v: [*]u8, i: u32, on: Bool) -> () {
  on ? { v[i] = u8(1) } | { }
}

swap: (v: [*]u8, i: u32, j: u32) -> () {
  a: u8 = v[i]
  b: u8 = v[j]
  v[i] = b
  v[j] = a
}

fill: (v: [*]u32, n: u32, x: u32) -> () {
  i: u32 = u32(0)
  while i < n {
    v[i] = x
    i = i + u32(1)
  }
}

main: (): i32 {
  buf: [8]u32
  bytes: [8]u8
  put(span(&buf), u32(1), u32(9))
  put3(span(&buf), u32(2), u32(5), u32(6))
  assert(buf[1] == u32(9))
  assert(buf[2] == u32(5))
  assert(buf[3] == u32(6))
  assert(buf[4] == u32(3))
  assert(bump(span(&buf), u32(1)) == u32(20))
  assert(buf[1] == u32(10))
  set_flag(span(&bytes), u32(2), true)
  set_flag(span(&bytes), u32(3), false)
  assert(bytes[2] == u8(1))
  assert(bytes[3] == u8(0))
  bytes[4] = u8(7)
  swap(span(&bytes), u32(2), u32(4))
  assert(bytes[2] == u8(7))
  assert(bytes[4] == u8(1))
  fill(span(&buf), u32(3), u32(11))
  assert(buf[0] == u32(11))
  assert(buf[2] == u32(11))
  assert(buf[3] == u32(6))
  42
}
`

func TestE2ENativeSpanEffects(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("effects.oak", nativeSpanEffectsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_span_effects", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native span effects: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"put", "put3", "set_flag", "swap"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body in the span memory it writes (v)") {
			t.Errorf("%s must be proven in its span memory; diagnostics:\n%s", fn, joined)
		}
	}
	if !strings.Contains(joined, "asm unit bump: proven equal to its Oak body") || !strings.Contains(joined, "and the span memory it writes (v)") {
		t.Errorf("bump must be proven in its result and its span memory; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit fill: not verified (") {
		t.Errorf("fill stores inside a data-dependent loop and must stay trusted; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_span_effects_c", New().WithSource("effects.oak", nativeSpanEffectsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
