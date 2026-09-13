package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record local without an initializer is zero storage
// (docs/spec/90-backend.md §6): the native backend zero-fills its slots
// as the C emitter's `{0}` and the interpreter's zero value do, so a field
// read before any write is zero and a body that fills its result record
// field by field (the prover's bit-vector helpers) lowers natively.
const nativeZeroRecordProgram = `
Bits: type = struct { lo: u32, hi: u32, w: u16, tag: u8, ok: Bool }

fill: (x: u32) -> u32 {
  out: Bits
  before: u32 = out.lo + out.hi + u32(out.w) + u32(out.tag) + (out.ok ? u32(100) | u32(0))
  out.lo = x
  out.hi = x * u32(2)
  out.w = u16(7)
  out.tag = u8(3)
  out.ok = true
  before + out.lo + out.hi + u32(out.w) + u32(out.tag) + (out.ok ? u32(1) | u32(0))
}

main: (): i32 {
  assert(fill(u32(10)) == u32(41))
  42
}
`

func TestE2ENativeZeroRecord(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("zero.oak", nativeZeroRecordProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_zero_record", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native zero record: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit fill:") {
		t.Errorf("fill was not lowered by the native backend; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_zero_record_c", New().WithSource("zero.oak", nativeZeroRecordProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_zero_record_portable", New().WithSource("zero.oak", nativeZeroRecordProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
