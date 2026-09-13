package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Leaf functions live in the argument registers (docs/spec/94-assembler.md
// §9, twentieth increment): a function that makes no call keeps its scalar
// parameters where they arrived, places its locals in the argument
// registers no parameter occupies before any callee-saved register, and
// saves nothing for them. Parameters assigned in the body, a local written
// in a loop, a parameter read after the result is staged in one arm, a
// float result beside integer homes, and a leaf with more locals than free
// argument registers all keep their meaning; the C backend's realization of
// the same program is the oracle, and the scalar leaves stay proven.
const nativeLeafProgram = `
mix: (a: u32, b: u32, c: u32) -> u32 {
  t: u32 = a * u32(3)
  u: u32 = b ^ c
  t + u
}

// Parameters assigned in place.
clamp_step: (x: u32, step: u32, limit: u32) -> u32 {
  x = x + step
  x > limit ? { x = limit } | { }
  x
}

// A local counter in an argument register, across a loop.
count_bits: (v: u32) -> u32 {
  n: u32 = u32(0)
  while v != u32(0) {
    n = n + (v & u32(1))
    v = v >> u32(1)
  }
  n
}

// An arm stages the result while the other arm still reads a parameter.
pick: (flag: Bool, a: u32, b: u32) -> u32 = flag ? a + u32(1) | b + u32(2)

// A float result: the integer homes are declared clobbers, x0 is no result.
scaled: (n: u32, k: u32) -> f64 {
  m: u32 = n * k
  f64_round_u32(m)
}

// More locals than free argument registers: the rest take callee-saved
// registers as before.
many: (a: u32, b: u32, c: u32, d: u32, e: u32, f: u32) -> u32 {
  p: u32 = a + b
  q: u32 = c + d
  r: u32 = e + f
  s: u32 = p * q
  t: u32 = q * r
  u: u32 = s ^ t
  v: u32 = u + p
  w: u32 = v + q
  w + r
}

main: (): i32 {
  assert(mix(u32(2), u32(5), u32(3)) == u32(12))
  assert(clamp_step(u32(7), u32(4), u32(10)) == u32(10))
  assert(clamp_step(u32(1), u32(4), u32(10)) == u32(5))
  assert(count_bits(u32(0xF0F0)) == u32(8))
  assert(pick(true, u32(40), u32(0)) == u32(41))
  assert(pick(false, u32(0), u32(40)) == u32(42))
  assert(scaled(u32(6), u32(7)) == 42.0)
  assert(many(u32(1), u32(2), u32(3), u32(4), u32(5), u32(6)) == u32(109))
  42
}
`

func TestE2ENativeLeaves(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("leaves.oak", nativeLeafProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_leaves", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native leaves: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"mix", "clamp_step", "count_bits", "pick", "scaled", "many", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// (clamp_step assigns a parameter, which the verifier's Oak side does
	// not model; many's products exceed the node budget and are witnessed.)
	for _, fn := range []string{"mix", "pick"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_leaves_c", New().WithSource("leaves.oak", nativeLeafProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_leaves_portable", New().WithSource("leaves.oak", nativeLeafProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
