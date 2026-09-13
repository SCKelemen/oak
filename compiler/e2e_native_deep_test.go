package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Deep expressions (the OS pilot's N6): an expression tree whose live
// operands exceed the seven scratch registers left the function to the C
// backend. The generator now widens the pool — x16/x17 in a function
// without calls, then unclaimed callee-saved registers, saved and restored
// — so the trees of depth 4 and 5 below lower natively and agree with the
// C backend; depth 3 always did.
func deepTree(depth, i int) string {
	if depth == 0 {
		return fmt.Sprintf("s[u32(%d)]", i%16)
	}
	return fmt.Sprintf("(%s + %s) * (%s ^ %s)", deepTree(depth-1, 2*i), deepTree(depth-1, 2*i+1), deepTree(depth-1, 2*i+2), deepTree(depth-1, 2*i+3))
}

func nativeDeepProgram() string {
	var b strings.Builder
	for _, depth := range []int{3, 4, 5} {
		fmt.Fprintf(&b, "deep%d: (s: []u32): u32 {\n  len(s) >= u32(16) ? { %s } | { u32(0) }\n}\n\n", depth, deepTree(depth, 0))
	}
	b.WriteString("main: (): i32 {\n  s: [16]u32\n  i: u32 = u32(0)\n  while i < u32(16) {\n    s[i] = i * u32(3) + u32(1)\n    i = i + u32(1)\n  }\n  i32_bits_u32((deep3(view(&s)) + deep4(view(&s)) + deep5(view(&s))) & u32(127))\n}\n")
	return b.String()
}

func TestE2ENativeDeepExpressions(t *testing.T) {
	requireArm64Host(t)
	program := nativeDeepProgram()
	var infos []string
	comp := New().WithSource("deep.oak", program).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, native, abnormal := buildAndRunFrom(t, "native_deep", comp)
	joined := strings.Join(infos, "\n")
	if abnormal {
		t.Fatalf("native: abnormal exit\n%s", joined)
	}
	for _, fn := range []string{"deep3", "deep4", "deep5"} {
		if !strings.Contains(joined, "asm unit "+fn+":") {
			t.Errorf("%s must lower natively; diagnostics:\n%s", fn, joined)
		}
	}
	_, c, abnormal := buildAndRunFrom(t, "native_deep_c", New().WithSource("deep.oak", program))
	if abnormal || c != native {
		t.Fatalf("C backend: exit = (%d, abnormal=%v); native %d", c, abnormal, native)
	}
}
