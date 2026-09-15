package compiler

// Scalar float stores through a span (`ys[i] = x` over `[*]f32`, the
// native lowering's `str sN, [xB, wI, uxtw #2]`) are decided by the
// verifier like every float value — up to the IEEE operations
// (docs/spec/94-assembler.md §8): the write log takes the register's low
// lane at the element's width, in a loop body too. Before this, a unit
// storing an f32 to a span was trusted ("a vector-register store to a span
// through the s view") while the f64 store (`str dN`) already proved — the
// SIMD pilot's kernels write f32 spans in loops.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeFloatSpanStoreProgram = `fill: (ys: [*]f32, v: f32): u32 {
  i: u32 = u32(0)
  while i < len(ys) {
    ys[i] = v + f32_round_u32(i)
    i = i + u32(1)
  }
  i
}

scale: (ys: [*]f32, k: f32): u32 {
  i: u32 = u32(0)
  while i < len(ys) {
    ys[i] = ys[i] * k
    i = i + u32(1)
  }
  i
}

set_one: (ys: [*]f64, at: u32, v: f64): u32 {
  at < len(ys) ? { ys[at] = v
  u32(1) } | { u32(0) }
}

main: (): i32 {
  buf: [4]f32 = [4]f32{0.0, 0.0, 0.0, 0.0}
  n: u32 = fill(span(&buf), 1.5)
  m: u32 = scale(span(&buf), 2.0)
  d: [2]f64 = [2]f64{0.0, 0.0}
  k: u32 = set_one(span(&d), u32(1), 3.0)
  (n == u32(4) && m == u32(4) && k == u32(1) && buf[3] == 9.0 && d[1] == 3.0) ? 42 | 1
}
`

func TestE2ENativeFloatSpanStores(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("float_span_store.oak", nativeFloatSpanStoreProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "float_span_store", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"fill", "scale", "set_one", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"fill", "scale"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body at the bit level") || !strings.Contains(joined, "span memory it writes (ys)") {
			t.Errorf("%s's span writes were not decided; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "float_span_store_c", New().WithSource("float_span_store.oak", nativeFloatSpanStoreProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
