package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
)

// Span locals and value-less record locals on the rv64 lane
// (docs/spec/94-assembler.md §9): `whole: []u32 = view(&buf)` binds the
// array's frame address and constant length in callee-saved registers, so
// the local reads, stores, and passes on like a parked span parameter; a
// record local without an initializer is zero-filled from the zero
// register. The program runs on the bare machine under QEMU against the C
// backend's realization, and natively on an AArch64 host.
const nativeSpanLocalsProgram = `Pair: type = struct { lo: u32, hi: u32 }

sum: (v: []u32) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(v) {
    acc = acc + v[i]
    i = i + u32(1)
  }
  acc
}

fill9: (w: [*]u32) -> () {
  w[1] = u32(9)
}

main: (): i32 {
  buf: [4]u32
  buf[0] = u32(1)
  buf[3] = u32(19)
  fill9(span(&buf))
  whole: []u32 = view(&buf)
  p: Pair
  p.lo = u32(3)
  i32_bits_u32(sum(whole) + whole[1] + len(whole) + p.lo + p.hi - u32(3))
}
`

func TestE2ENativeRV64SpanLocals(t *testing.T) {
	_, infos := nativeRV64Lower(t, rv64Linux, nativeSpanLocalsProgram)
	joined := strings.Join(infos, "\n")
	for _, fn := range []string{"sum", "fill9", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the rv64 lane; diagnostics:\n%s", fn, joined)
		}
	}
	for _, fn := range []string{"sum", "fill9"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven by the verifier; diagnostics:\n%s", fn, joined)
		}
	}
	skipInShort(t)
	bare := target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}
	bareNative, _ := nativeRV64Lower(t, bare, nativeSpanLocalsProgram)
	if out := runNativeRV64BareABI(t, "native_rv64_span_locals", bareNative, false); !strings.Contains(out, "0000002a\n") {
		t.Fatalf("the span-locals program under QEMU did not exit 42:\n%s", out)
	}
}

// The same program on the AArch64 lane: the two lanes agree with the C
// backend.
func TestE2ENativeSpanLocals(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("locals.oak", nativeSpanLocalsProgram).WithNativeBodies().WithNativeAsm()
	if _, code, abnormal := buildAndRunFrom(t, "native_span_locals", comp); abnormal || code != 42 {
		t.Fatalf("native span locals: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_span_locals_c", New().WithSource("locals.oak", nativeSpanLocalsProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
