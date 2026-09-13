package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Call summaries in the verifier (docs/spec/94-assembler.md §8): a native
// body that calls a program function with a scalar signature is proven
// against its Oak body with the callee taken at its own Oak body, on both
// lanes, instead of trusted for the call. The callees are `pub`, so the
// source-level inlining pass leaves the calls in place; the program's
// result checks the summary's modeling of a narrow result (the u8 the
// caller widens) and runs the same through C.
const nativeCallSummaryProgram = `pub inc: (a: u32) -> u32 = a + u32(1)
pub twice: (a: u32) -> u32 = inc(a) + inc(a)
pub clamp8: (v: u32) -> u8 = v > u32(255) ? u8(255) | u8_trunc_u32(v)
pub after: (v: u32) -> u32 = u32(clamp8(v)) + u32(1)

main: (): i32 {
  i32_bits_u32(twice(u32(3)) + after(u32(300)) - u32(264))
}
`

func TestE2ENativeCallSummaries(t *testing.T) {
	for _, tname := range []string{"freestanding/arm64", "linux/riscv64"} {
		tgt, err := target.Parse(tname)
		if err != nil {
			t.Fatal(err)
		}
		var native []string
		sink := func(d *diagnostic.Diagnostic) {
			if strings.HasPrefix(d.Message, "native backend: ") {
				native = append(native, d.Message)
			}
		}
		comp := New().WithSource("calls.oak", nativeCallSummaryProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		for _, fn := range []string{"twice", "after"} {
			found := false
			for _, m := range native {
				if !strings.Contains(m, "asm unit "+fn+":") && !strings.Contains(m, "asm unit "+fn+" ") {
					continue
				}
				found = true
				if !strings.Contains(m, "proven") || !strings.Contains(m, "callees taken at their Oak bodies") {
					t.Errorf("%s: %s: want a proof through the callee's Oak body, got: %s", tname, fn, m)
				}
			}
			if !found {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, strings.Join(native, "\n"))
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_call_summaries", New().WithSource("calls.oak", nativeCallSummaryProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
