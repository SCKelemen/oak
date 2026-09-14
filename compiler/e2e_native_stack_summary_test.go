package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A call summary reads arguments beyond the eight registers from the
// caller's outgoing area (docs/spec/94-assembler.md §9, thirtieth
// increment): the slots are frame slots the executor holds as the caller
// stored them, laid out by the shared rule (asm/abi.go), each scalar at
// its natural size. The callee mixes widths so that the packed and the
// 8-byte-slot conventions both place them; the C backend is the oracle.
const nativeStackSummaryProgram = `
put_mix: (v: [*]u32, a: u32, b: u64, c: u8, d: u32, e: u32, f: u32, g: u16, h: u32, i: u64, on: Bool) -> () {
  v[0] = a + u32_trunc_u64(b) + u32(c) + d
  v[1] = e + f + u32(g) + h + u32_trunc_u64(i) + (on ? u32(1000) | u32(0))
}

put_all: (v: [*]u32, k: u32) -> () {
  put_mix(v, k, u64(k) + u64(1), u8(2), k + u32(3), k + u32(4), k + u32(5), u16(6), k + u32(7), u64(k) + u64(8), k > u32(10))
}

sum_after: (v: [*]u32, k: u32) -> u32 {
  put_all(v, k)
  v[0] + v[1]
}

main: (): i32 {
  buf: [4]u32
  put_all(span(&buf), u32(1))
  assert(buf[0] == u32(1) + u32(2) + u32(2) + u32(4))
  assert(buf[1] == u32(5) + u32(6) + u32(6) + u32(8) + u32(9))
  assert(sum_after(span(&buf), u32(20)) == (u32(20) + u32(21) + u32(2) + u32(23)) + (u32(24) + u32(25) + u32(6) + u32(27) + u32(28) + u32(1000)))
  42
}
`

func TestE2ENativeStackSummary(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("stack_summary.oak", nativeStackSummaryProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_stack_summary", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native stack summary: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit put_all: proven equal to its Oak body in the span memory it writes (v)") {
		t.Errorf("put_all passes three arguments on the stack and must be proven through the summary; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit sum_after: proven equal to its Oak body") || !strings.Contains(joined, "and the span memory it writes (v)") {
		t.Errorf("sum_after must be proven in its result and its span memory; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_stack_summary_c", New().WithSource("stack_summary.oak", nativeStackSummaryProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
