package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Call liveness for the caller-saved homes (docs/spec/94-assembler.md §9,
// twenty-third increment): a home is saved around a call only when its
// variable is read afterward, and a variable never live across a call takes
// a caller-saved home before a callee-saved register. The shapes the
// numbering must get right: a value read in place as an operand after a
// call in the same expression (`v + f(x)`), a call's argument read before
// the call, a loop-carried variable read before the loop's call, an index
// assignment whose value calls before the index is read in place, and a
// variable dead before the calls that follow it. The C backend's
// realization is the oracle; the seam checker refuses any home read after
// a call that did not restore it.
const nativeCallLivenessProgram = `
f: (x: u32) -> u32 = x * u32(2) + u32(1)
g: (x: u32, y: u32) -> u32 = x ^ y

operand_after_call: (a: u32, b: u32) -> u32 {
  v: u32 = a + b
  w: u32 = v + f(a)
  w + v
}

argument_before_call: (a: u32) -> u32 {
  t: u32 = a + u32(3)
  u: u32 = f(t)
  s: u32 = g(u, u32(5))
  s + u32(1)
}

loop_carried: (n: u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  step: u32 = u32(2)
  while i < n {
    acc = acc + step
    acc = acc + f(i)
    i = i + u32(1)
  }
  acc + step
}

store_after_call: (out: [*]u32, k: u32) -> u32 {
  at: u32 = k + u32(1)
  out[at] = f(k)
  out[at + u32(1)] = g(k, at)
  at
}

dead_before_calls: (a: u32, b: u32) -> u32 {
  p: u32 = a * b
  q: u32 = p + u32(1)
  r: u32 = f(q)
  s: u32 = f(r)
  t: u32 = g(s, r)
  t + u32(2)
}

main: (): i32 {
  assert(operand_after_call(u32(3), u32(4)) == u32(21))
  assert(argument_before_call(u32(4)) == u32(11))
  assert(loop_carried(u32(3)) == u32(17))
  buf: [8]u32
  assert(store_after_call(span(&buf), u32(2)) == u32(3))
  assert(buf[3] == u32(5))
  assert(buf[4] == u32(1))
  assert(dead_before_calls(u32(2), u32(3)) == u32(18))
  42
}
`

func TestE2ENativeCallLiveness(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("liveness.oak", nativeCallLivenessProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_call_liveness", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native call liveness: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"operand_after_call", "argument_before_call", "loop_carried", "store_after_call", "dead_before_calls", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_call_liveness_c", New().WithSource("liveness.oak", nativeCallLivenessProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_call_liveness_portable", New().WithSource("liveness.oak", nativeCallLivenessProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
