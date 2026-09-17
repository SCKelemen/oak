package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Owned arrays of scalars as values through the native backend
// (docs/spec/94-assembler.md §9, forty-seventh increment): `[N]T`
// parameters, results, arguments, whole-array assignments and stores
// (`next.h = bump(next.h, 1)`) follow the record rules under the one-field
// composite the C backend's wrapper struct is — chunks in x0/x1 up to 16
// bytes, by reference (and results through x8) beyond. The C backend's
// realization of the same program is the oracle.
const nativeArrayValueProgram = `
Digest: type = struct {
  h: [8]u32
  count: u32
}

// A 32-byte array parameter arrives by reference and is read in place.
sum8: (h: [8]u32) -> u32 = h[0] + h[1] + h[2] + h[3] + h[4] + h[5] + h[6] + h[7]

// The verifier unrolls this loop: h[i] then has a constant register index.
sum8_loop: (h: [8]u32) -> u32 {
  total: u32 = u32(0)
  i: u32 = u32(0)
  while i < u32(8) {
    total = total + h[i]
    i = i + u32(1)
  }
  total
}

// An 8-byte array arrives in one register chunk, a 16-byte one in two.
pair_sum: (v: [2]u32) -> u32 = v[0] + v[1]
quad_sum: (v: [4]u32) -> u32 = v[0] + v[1] * u32(2) + v[2] * u32(3) + v[3] * u32(4)

// A 32-byte array result is written through x8; an 8-byte one comes back in x0.
bump: (h: [8]u32, by: u32) -> [8]u32 {
  out: [8]u32 = h
  i: u32 = u32(0)
  while i < len(out) {
    out[i] = out[i] + by
    i = i + u32(1)
  }
  out
}
halves: (x: u32) -> [2]u32 = [2]u32{ x & u32(0xffff), x >> u32(16) }

// A whole array field stored from a call's result.
step: (d: Digest) -> Digest {
  next: Digest = d
  next.h = bump(next.h, u32(1))
  next.count = next.count + u32(1)
  next
}

main: (): i32 {
  seed: [8]u32 = [8]u32{ 1, 2, 3, 4, 5, 6, 7, 8 }
  d: Digest
  d.h = seed
  d.count = u32(0)
  d = step(step(d))
  total: u32 = sum8(d.h)
  assert(total == u32(52))
  assert(sum8_loop(d.h) == total)
  h2: [2]u32 = halves(u32(0x00030002))
  assert(pair_sum(h2) == u32(5))
  q: [4]u32 = [4]u32{ 1, 1, 1, 1 }
  assert(quad_sum(q) == u32(10))
  seed = bump(seed, u32(2))
  assert(sum8(seed) == u32(52))
  assert(total + pair_sum(h2) + quad_sum(q) + d.count + u32(25) - sum8(seed) == u32(42))
  42
}
`

func TestE2ENativeArrayValues(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("array_values.oak", nativeArrayValueProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_array_values", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native array values: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum8", "sum8_loop", "pair_sum", "quad_sum", "bump", "halves", "step", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"sum8", "sum8_loop", "pair_sum", "quad_sum", "halves"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (array leaves as parameters, a chunked array result); diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_array_values_c", New().WithSource("array_values.oak", nativeArrayValueProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
