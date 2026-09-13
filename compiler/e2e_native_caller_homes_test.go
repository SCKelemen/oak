package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Caller-saved homes in a function that calls (docs/spec/94-assembler.md
// §9, twenty-second increment): once the ten callee-saved registers are
// taken, a variable lives in x16, x17, or a free argument register, saved
// before each call and restored after it, instead of a frame slot touched
// on every read and write; a value just stored to a slot variable is read
// back from the register that stored it. A body with more live variables
// than callee-saved registers, all read after calls (including a call whose
// arguments hold a call), keeps its meaning; the C backend's realization is
// the oracle.
const nativeCallerHomesProgram = `
step: (v: u32) -> u32 = v * u32(3) + u32(1)
pair: (a: u32, b: u32) -> u32 = a ^ (b << u32(1))

busy: (p0: u32, p1: u32, p2: u32, p3: u32) -> u32 {
  a: u32 = step(p0)
  b: u32 = step(p1)
  c: u32 = step(p2)
  d: u32 = step(p3)
  e: u32 = a + b
  f: u32 = c + d
  g: u32 = pair(e, f)
  h: u32 = pair(a, step(b))
  i: u32 = pair(step(c), d)
  j: u32 = g + h + i
  k: u32 = pair(j, e) + pair(f, g)
  t: u32 = step(k)
  t != u32(0) ? { k = k + t } | { k = a }
  a + b + c + d + e + f + g + h + i + j + k + p0 + p1 + p2 + p3
}

main: (): i32 {
  r: u32 = busy(u32(1), u32(2), u32(3), u32(4))
  assert(r == u32(887))
  42
}
`

func TestE2ENativeCallerHomes(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("callerhomes.oak", nativeCallerHomesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_caller_homes", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native caller homes: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"step", "pair", "busy", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_caller_homes_c", New().WithSource("callerhomes.oak", nativeCallerHomesProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_caller_homes_portable", New().WithSource("callerhomes.oak", nativeCallerHomesProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
