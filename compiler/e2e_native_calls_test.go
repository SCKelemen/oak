package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Calls through the native backend's verifier (docs/spec/94-assembler.md
// §9, calls): a body that calls a program function of scalar parameters
// and result is proven, not trusted, once the callee's own unit is —
// the verifier decides `bl f` by f's Oak body over the argument registers
// and forgets what the callee owns. The compiler verifies callees first,
// whatever the source order. The C backend's realization is the oracle.
const nativeCallsProgram = `
// The callees carry a counted loop so the compiler's helper inliner leaves
// them as calls (discipline.InlineHelperShape) and the machine bodies say bl.

// A caller before its callee in the source: verified after it.
clamp_sum: (a: u32, b: u32, hi: u32) -> u32 = clamp_loop(a + b, hi)

// x, or hi when x is above it, decided over four halvings.
clamp_loop: (x: u32, hi: u32) -> u32 {
  r: u32 = x
  i: u32 = u32(0)
  while i < u32(4) {
    r = r > hi ? hi | r
    i = i + u32(1)
  }
  r
}

// x + 0 + 1 + 2 + 3.
sum4: (x: u32) -> u32 {
  acc: u32 = x
  i: u32 = u32(0)
  while i < u32(4) {
    acc = acc + i
    i = i + u32(1)
  }
  acc
}

twice_sum4: (x: u32) -> u32 = sum4(sum4(x))

// The low byte plus two, wrapping: a narrow result consumed at its width.
low_byte_plus2: (x: u32) -> u8 {
  r: u8 = u8_trunc_u32(x)
  i: u32 = u32(0)
  while i < u32(2) {
    r = r + u8(1)
    i = i + u32(1)
  }
  r
}

byte_sum: (x: u32, y: u32) -> u32 = u32(low_byte_plus2(x)) + u32(low_byte_plus2(y))

// x < 16, as four halvings reaching zero: a Bool result in a condition.
is_small: (x: u32) -> Bool {
  n: u32 = x
  i: u32 = u32(0)
  while i < u32(4) {
    n = n >> u32(1)
    i = i + u32(1)
  }
  n == u32(0)
}

pick: (x: u32, y: u32) -> u32 = is_small(x) ? y | x

main: (): i32 {
  assert(twice_sum4(u32(5)) == u32(17))
  assert(clamp_sum(u32(30), u32(20), u32(40)) == u32(40))
  assert(clamp_sum(u32(3), u32(4), u32(40)) == u32(7))
  assert(byte_sum(u32(0x1FF), u32(0x201)) == u32(4))
  assert(pick(u32(3), u32(9)) == u32(9))
  assert(pick(u32(30), u32(9)) == u32(30))
  42
}
`

func TestE2ENativeCalls(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("calls.oak", nativeCallsProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_calls", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native calls: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum4", "clamp_loop", "low_byte_plus2", "is_small"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal") {
			t.Errorf("the callee %s must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	for fn, callee := range map[string]string{"twice_sum4": "sum4", "clamp_sum": "clamp_loop", "byte_sum": "low_byte_plus2", "pick": "is_small"} {
		want := "asm unit " + fn + ": proven equal"
		if !strings.Contains(joined, want) {
			t.Errorf("the caller %s must be proven through its callee's unit; diagnostics:\n%s", fn, joined)
		}
		if !strings.Contains(joined, "the call to "+callee+" by its proven unit") {
			t.Errorf("the verdict of %s must name the call to %s; diagnostics:\n%s", fn, callee, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_calls_c", New().WithSource("calls.oak", nativeCallsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
