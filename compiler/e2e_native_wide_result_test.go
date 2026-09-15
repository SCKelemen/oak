package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record result beyond two register chunks is returned through the area
// the caller passes in x8 (docs/spec/94-assembler.md §9): the verifier
// models the area as frame memory of its own, the body's stores tile it,
// and each word of the record is verified as a chunk of its own against
// the Oak record's leaves. The C backend is the oracle for the values.
const nativeWideResultProgram = `
Wide: type = struct { a: u64, b: u64, c: u32, d: u8 }

mk_wide: (x: u64, k: u32) -> Wide = Wide { a: x, b: x + u64(1), c: k * u32(3), d: u8(7) }

wide_sum: (x: u64, k: u32) -> u64 {
  w: Wide = mk_wide(x, k)
  w.a + w.b + u64(w.c) + u64(w.d)
}

main: (): i32 {
  w: Wide = mk_wide(u64(10), u32(2))
  assert(w.a == u64(10))
  assert(w.b == u64(11))
  assert(w.c == u32(6))
  assert(w.d == u8(7))
  assert(wide_sum(u64(1), u32(1)) == u64(13))
  42
}
`

func TestE2ENativeWideResult(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("wide.oak", nativeWideResultProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_wide_result", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native wide result: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit mk_wide: proven equal to its Oak body") {
		t.Errorf("mk_wide returns its record through the result area and must be proven chunk by chunk; diagnostics:\n%s", joined)
	}
	// The caller passes the area in x8; the summary of mk_wide stores the
	// record's leaves there, and wide_sum's loads read them.
	if !strings.Contains(joined, "asm unit wide_sum: proven equal to its Oak body") {
		t.Errorf("wide_sum calls a callee returning its record through memory and must be proven; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_wide_result_c", New().WithSource("wide.oak", nativeWideResultProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
