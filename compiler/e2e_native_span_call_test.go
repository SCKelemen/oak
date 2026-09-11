package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Span parameters in functions that call (docs/spec/94-assembler.md §9,
// fifth increment): the prologue parks the {base, len} pair in callee-saved
// registers (the checker follows the copies), so a span function may call
// helpers, forward its span to them, and keep walking it afterwards. The C
// backend's realization of the same program is the oracle.
const nativeSpanCallProgram = `
at: (v: []u32, i: u32) -> u32 = v[i]

mul: (a: u32, b: u32) -> u32 = a * b

// Forwards its view twice and reads len(v) after the calls.
ends: (v: []u32) -> u32 = at(v, u32(0)) * u32(100) + at(v, len(v) - u32(1))

// Stores through a span around a call inside the loop: the value comes
// from a callee, the index guard is re-established before every access.
scale: (s: [*]u32, k: u32) -> () {
  i: u32 = u32(0)
  while i < len(s) {
    s[i] = mul(s[i], k)
    i = i + u32(1)
  }
}

// Two views parked in four callee-saved registers: one walked directly, the
// other forwarded to a leaf inside the loop, after a call before the loop.
dot_after: (a: []u32, b: []u32) -> u32 {
  acc: u32 = at(a, u32(0))
  i: u32 = u32(0)
  while i < len(a) {
    acc = acc + a[i] * at(b, i)
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  xs: [4]u32 = [u32(3), u32(5), u32(7), u32(9)]
  assert(ends(view(&xs)) == u32(309))
  ys: [4]u32 = [u32(1), u32(1), u32(1), u32(1)]
  scale(span(&ys), u32(2))
  assert(ys[3] == u32(2))
  assert(dot_after(view(&xs), view(&ys)) == u32(51))
  scale(span(&ys), u32(10))
  assert(ys[0] == u32(20))
  42
}
`

func TestE2ENativeSpanCalls(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("span_calls.oak", nativeSpanCallProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_span_calls", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native span calls: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"at", "mul", "ends", "scale", "dot_after", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_span_calls_c", New().WithSource("span_calls.oak", nativeSpanCallProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_span_calls_portable", New().WithSource("span_calls.oak", nativeSpanCallProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
