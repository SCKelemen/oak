package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// The native backend (docs/spec/94-assembler.md §9, nativegen): ordinary
// Oak functions in the fixed-width integer subset are lowered to checked
// asm functions, verified against their own bodies, encoded by the Oak
// assembler, and run — with the C backend's realization of the same program
// as the oracle (the portable lowering compiles the Oak bodies instead).
const nativeProgram = `
// Wrapping arithmetic, shifts, comparisons, conversions.
mix: (a: u32, b: u32) -> u32 = ((a + b) * u32(3)) ^ (a >> u32(2))

// Narrow types stay normalized: the byte sum wraps at 256.
byte_sum: (a: u8, b: u8) -> u8 = a + b

// Signed narrow arithmetic and comparison.
clamp8: (x: i8) -> i8 = x < i8(0) ? i8(0) | x

// Division and remainder with the C helpers' edge cases.
divmod: (a: i32, b: i32) -> i32 = (a / b) * i32(100) + a % b

// Conditionals, short-circuit, Bool results.
between: (x: u64, lo: u64, hi: u64) -> Bool = x >= lo && x < hi

// Locals, a counted loop, break.
sum_to: (n: u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i <= n {
    i == u32(1000) ? { break } | { }
    acc = acc + i
    i = i + u32(1)
  }
  acc
}

// Calls between natively compiled functions, with live temporaries across
// the call.
combine: (a: u32, b: u32) -> u32 = mix(a, b) + sum_to(a) + mix(b, a)

// Tail recursion (the discipline admits only tail self-calls): a call to
// itself with the accumulator threaded through.
fact: (n: u64, acc: u64) -> u64 = n == u64(0) ? acc | fact(n - u64(1), acc * n)

// A unit function with an effect.
check_all: (a: u32) -> () {
  assert(mix(a, a) == mix(a, a))
}

// Widening and narrowing conversions.
widen: (x: i32) -> i64 = i64(x) - i64(1)
narrow: (x: u64) -> u16 = u16_trunc_u64(x)

main: (): i32 {
  assert(mix(u32(5), u32(7)) == u32(37))
  assert(byte_sum(u8(200), u8(100)) == u8(44))
  assert(clamp8(i8(-5)) == i8(0))
  assert(clamp8(i8(9)) == i8(9))
  assert(divmod(i32(-7), i32(2)) == i32(-301))
  assert(between(u64(5), u64(1), u64(10)))
  assert(!between(u64(10), u64(1), u64(10)))
  assert(sum_to(u32(10)) == u32(55))
  assert(sum_to(u32(5000)) == u32(499500))
  assert(combine(u32(3), u32(4)) == u32(mix(u32(3), u32(4)) + sum_to(u32(3)) + mix(u32(4), u32(3))))
  assert(fact(u64(10), u64(1)) == u64(3628800))
  check_all(u32(9))
  assert(widen(i32(-1)) == i64(-2))
  assert(narrow(u64(0x1FFFF)) == u16(0xFFFF))
  42
}
`

func TestE2ENativeBodies(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("native.oak", nativeProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_bodies", comp)
	if abnormal || code != 42 {
		t.Fatalf("native bodies: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"mix", "byte_sum", "clamp8", "divmod", "between", "sum_to", "combine", "fact", "check_all", "widen", "narrow", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"mix", "byte_sum", "clamp8", "between", "widen", "narrow"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body; diagnostics:\n%s", fn, joined)
		}
	}
	// The same program through the C backend alone, and the native build's
	// portable realization, agree.
	if _, code, abnormal := buildAndRunFrom(t, "native_bodies_c", New().WithSource("native.oak", nativeProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_bodies_portable", New().WithSource("native.oak", nativeProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// Spans and views through the native backend: the guarded element idiom
// (`cmp wI, wL; b.hs trap; ldr [base, wI, uxtw #s]`) for loads and stores,
// `len`, the tail self-call as a loop, and an out-of-range index trapping
// in both realizations.
const nativeSpanProgram = `
sum: (v: []u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

// Bytes are read zero-extended, halfwords signed where the element is.
byte_total: (b: []u8) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(b) {
    acc = acc + u32(b[i])
    i = i + u32(1)
  }
  acc
}

fill: (s: [*]u16, x: u16) -> () {
  i: u32 = u32(0)
  while i < len(s) {
    s[i] = x + u16_trunc_u32(i)
    i = i + u32(1)
  }
}

at: (v: []u32, i: u32) -> u32 = v[i]

// A tail self-call: the loop form.
count_down: (n: u32, acc: u32) -> u32 = n == u32(0) ? acc | count_down(n - u32(1), acc + n)

main: (): i32 {
  buf: [4]u32
  buf[0] = u32(10)
  buf[1] = u32(20)
  buf[2] = u32(5)
  buf[3] = u32(7)
  whole: []u32 = view(&buf)
  assert(sum(whole) == u32(42))
  assert(sum(subslice(whole, u32(0), u32(0))) == u32(0))
  assert(at(whole, u32(2)) == u32(5))
  bytes: [3]u8
  bytes[0] = u8(200)
  bytes[1] = u8(100)
  bytes[2] = u8(1)
  assert(byte_total(view(&bytes)) == u32(301))
  halves: [3]u16
  fill(span(&halves), u16(40))
  assert(halves[0] == u16(40))
  assert(halves[2] == u16(42))
  assert(count_down(u32(4), u32(0)) == u32(10))
  42
}
`

const nativeOutOfRangeProgram = `
at: (v: []u32, i: u32) -> u32 = v[i]

main: (): i32 {
  buf: [2]u32
  buf[0] = u32(1)
  buf[1] = u32(2)
  at(view(&buf), u32(2))
  0
}
`

func TestE2ENativeSpans(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("spans.oak", nativeSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_spans", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native spans: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum", "byte_total", "fill", "at", "count_down"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"at", "sum", "byte_total"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s must be proven equal to its Oak body (the guarded element load, the coupled loops); diagnostics:\n%s", fn, joined)
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_spans_c", New().WithSource("spans.oak", nativeSpanProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	// An index at the length traps in both realizations.
	_, _, nativeAbnormal := buildAndRunFrom(t, "native_oob", New().WithSource("oob.oak", nativeOutOfRangeProgram).WithNativeBodies().WithNativeAsm())
	_, _, cAbnormal := buildAndRunFrom(t, "native_oob_c", New().WithSource("oob.oak", nativeOutOfRangeProgram))
	if !nativeAbnormal || !cAbnormal {
		t.Fatalf("an out-of-range index must trap in both realizations (native abnormal=%v, C abnormal=%v)", nativeAbnormal, cAbnormal)
	}
}
