package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// By-reference record parameters read in place (docs/spec/94-assembler.md
// §9, eighteenth increment): a record beyond 16 bytes arrives as the
// address of the caller's copy; a body that only reads it keeps that
// address in a callee-saved register and loads the fields through it — no
// copy into the frame — and passes it on to a callee by the same address.
// A body that writes its parameter still copies it at entry, so the
// caller's record is untouched. The C backend's realization is the oracle.
const nativeRecordInPlaceProgram = `
Big: type = struct { a: u32, b: u32, c: u32, d: u32, e: u32, f: u64 }

sum_big: (r: Big) -> u32 = r.a + r.b + r.c + r.d + r.e + u32_trunc_u64(r.f)

// Passes r on by its address; the callee reads the caller's memory.
twice: (r: Big) -> u32 = sum_big(r) + sum_big(r)

// Writes its parameter: works on a copy of its own.
bump: (r: Big) -> u32 {
  r.a = r.a + u32(100)
  r.a + r.b
}

// Reads a field after a call that passed the record on.
after_call: (r: Big) -> u32 {
  s: u32 = sum_big(r)
  s + r.e
}

main: (): i32 {
  x: Big = Big { a: u32(1), b: u32(2), c: u32(3), d: u32(4), e: u32(5), f: u64(6) }
  assert(sum_big(x) == u32(21))
  assert(twice(x) == u32(42))
  assert(bump(x) == u32(103))
  assert(sum_big(x) == u32(21))
  assert(after_call(x) == u32(26))
  42
}
`

func TestE2ENativeRecordInPlace(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("inplace.oak", nativeRecordInPlaceProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_inplace", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native in-place records: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"sum_big", "twice", "bump", "after_call", "main"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s was not lowered by the native backend; diagnostics:\n%s", fn, joined)
		}
	}
	// The leaf over the parameter's leaves is proven, reads in place or not.
	if !strings.Contains(joined, "asm unit sum_big: proven") {
		t.Errorf("sum_big must be proven equal to its Oak body; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_inplace_c", New().WithSource("inplace.oak", nativeRecordInPlaceProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_inplace_portable", New().WithSource("inplace.oak", nativeRecordInPlaceProgram).WithNativeBodies(), "-DOAK_PORTABLE_INTRINSICS"); abnormal || code != 42 {
		t.Fatalf("portable realization: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
