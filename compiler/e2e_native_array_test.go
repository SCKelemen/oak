package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Owned arrays through the native backend (docs/spec/94-assembler.md §9,
// fourth increment): `buf: [N]T` locals live in the frame, zero-filled or
// initialized from a literal; `buf[i]` goes through the array's frame
// address under the constant guard `cmp wI, #N; b.hs trap` (a literal index
// addresses its slot through sp directly); `view(&buf)` and `span(&buf)`
// hand a callee the {frame address, N} pair; `len(buf)` is N. The C
// backend's realization of the same program is the oracle.
const nativeArrayProgram = `
sum: (v: []u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

fill: (s: [*]u16, x: u16) -> () {
  i: u32 = u32(0)
  while i < len(s) {
    s[i] = x
    i = i + u32(1)
  }
}

// A histogram in the frame: bytes bucketed into four owned counters, the
// index computed, not a literal.
buckets: (v: []u8) -> u32 {
  counts: [4]u32
  i: u32 = u32(0)
  while i < len(v) {
    b: u32 = u32(v[i]) >> u32(6)
    counts[b] = counts[b] + u32(1)
    i = i + u32(1)
  }
  counts[0] * u32(1000) + counts[1] * u32(100) + counts[2] * u32(10) + counts[3]
}

// An owned array passed on to a leaf: the frame address and length pair.
squares: () -> u32 {
  xs: [5]u32 = [u32(1), u32(4), u32(9), u32(16), u32(25)]
  sum(view(&xs))
}

// Zero-filled storage, filled through a span, read back by literal index.
filled: () -> u32 {
  buf: [6]u16
  fill(span(&buf), u16(7))
  u32(buf[5]) + u32(len(buf))
}

// Signed bytes round-trip with sign extension.
signed_bytes: (i: u32) -> i32 {
  bytes: [3]i8 = [i8(-1), i8(2), i8(-3)]
  i32(bytes[i])
}

// Float elements in the frame.
float_total: () -> f64 {
  xs: [3]f64 = [0.5, 1.5, 40.0]
  i: u32 = u32(0)
  acc: f64 = 0.0
  while i < len(xs) {
    acc = acc + xs[i]
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  assert(squares() == u32(55))
  assert(filled() == u32(13))
  assert(signed_bytes(u32(0)) == i32(-1))
  assert(signed_bytes(u32(2)) == i32(-3))
  assert(float_total() == 42.0)
  data: [8]u8
  data[0] = u8(10)
  data[1] = u8(70)
  data[2] = u8(130)
  data[3] = u8(200)
  data[4] = u8(255)
  data[7] = u8(64)
  assert(buckets(view(&data)) == u32(3212))
  42
}
`

// A computed index at the array's length traps in both realizations.
const nativeArrayOutOfRangeProgram = `
pick: (i: u32) -> u32 {
  xs: [4]u32 = [u32(1), u32(2), u32(3), u32(4)]
  xs[i]
}

main: (): i32 {
  pick(u32(4))
  0
}
`

func TestE2ENativeArrays(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("arrays.oak", nativeArrayProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_arrays", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native arrays: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum", "fill", "buckets", "squares", "filled", "signed_bytes", "float_total", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_arrays_c", New().WithSource("arrays.oak", nativeArrayProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_arrays_portable", New().WithSource("arrays.oak", nativeArrayProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	var trapInfos []string
	trapComp := New().WithSource("oob.oak", nativeArrayOutOfRangeProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			trapInfos = append(trapInfos, d.Message)
		}
	})
	_, _, nativeAbnormal := buildAndRunFrom(t, "native_array_oob", trapComp)
	if !strings.Contains(strings.Join(trapInfos, "\n"), "asm unit pick:") {
		t.Errorf("pick was not lowered by the native backend; diagnostics:\n%s", strings.Join(trapInfos, "\n"))
	}
	_, _, cAbnormal := buildAndRunFrom(t, "native_array_oob_c", New().WithSource("oob.oak", nativeArrayOutOfRangeProgram))
	if !nativeAbnormal || !cAbnormal {
		t.Fatalf("an index at the array's length must trap in both realizations (native abnormal=%v, C abnormal=%v)", nativeAbnormal, cAbnormal)
	}
}
