package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// An assert under the assembler verifier (docs/spec/94-assembler.md §9,
// "Asserts under the verifier"): a failed assert traps, the executor drops
// the trapping path, and the Oak side reads the statement as a no-op, so
// a body with an assert, and a caller of a unit callee that asserts, are
// proven over the inputs on which the asserts hold.
const nativeAssertCalleeProgram = `require_small: (n: u32) -> () {
  assert(n < u32(100))
}

scaled: (n: u32) -> u32 {
  require_small(n)
  n * u32(2)
}

halve_checked: (n: u32) -> u32 {
  assert(n > u32(1))
  n - u32(1)
}

main: (): i32 {
  i32_bits_u32(scaled(u32(21)) + halve_checked(u32(8)) - u32(49))
}
`

func TestE2ENativeAssertCallee(t *testing.T) {
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
		comp := New().WithSource("assert_callee.oak", nativeAssertCalleeProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		joined := strings.Join(native, "\n")
		for _, fn := range []string{"scaled", "halve_checked"} {
			verdict := ""
			for _, m := range native {
				if strings.Contains(m, "asm unit "+fn+":") {
					verdict = m
				}
			}
			if verdict == "" {
				t.Errorf("%s: %s: no native verdict:\n%s", tname, fn, joined)
				continue
			}
			if !strings.Contains(verdict, "proven equal") {
				t.Errorf("%s: %s must be proven with its assert a no-op: %s", tname, fn, verdict)
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_assert_callee", New().WithSource("assert_callee.oak", nativeAssertCalleeProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
