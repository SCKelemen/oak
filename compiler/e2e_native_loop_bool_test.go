package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// A Bool loop variable (docs/spec/94-assembler.md §9, "Bool loop
// variables"): `valid = false` inside a counted loop is a 1-bit Oak local
// held in a register as 0 or 1; the coupling pairs the two by
// zero-extension, so the body is proven rather than witnessed.
const nativeLoopBoolProgram = `all_ascii: (src: []u8) -> Bool {
  valid: Bool = true
  i: u32 = u32(0)
  while i < len(src) {
    src[i] > u8(127) ? { valid = false }
    i = i + u32(1)
  }
  valid
}

any_zero: (src: []u8, n: u32) -> u32 {
  found: Bool = false
  i: u32 = u32(0)
  while i < n {
    src[i] == u8(0) ? { found = true }
    i = i + u32(1)
  }
  found ? u32(1) | u32(0)
}

main: (): i32 {
  a: [4]u8 = [4]u8{65, 66, 67, 68}
  b: [4]u8 = [4]u8{1, 0, 3, 4}
  i32_bits_u32((all_ascii(view(&a)) ? u32(1) | u32(0)) + any_zero(view(&b), u32(4)) - u32(2))
}
`

func TestE2ENativeLoopBoolVariables(t *testing.T) {
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
		comp := New().WithSource("loop_bool.oak", nativeLoopBoolProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(sink)
		if _, err := comp.EmitC().Get(); err != nil {
			t.Fatalf("%s: native build: %v", tname, err)
		}
		joined := strings.Join(native, "\n")
		for _, fn := range []string{"all_ascii", "any_zero"} {
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
				t.Errorf("%s: %s must be proven with its Bool loop variable coupled: %s", tname, fn, verdict)
			}
		}
	}
	if _, exit, abnormal := buildAndRunFrom(t, "native_loop_bool", New().WithSource("loop_bool.oak", nativeLoopBoolProgram)); abnormal || exit != 0 {
		t.Fatalf("program: exit = (%d, abnormal=%v), want 0", exit, abnormal)
	}
}
