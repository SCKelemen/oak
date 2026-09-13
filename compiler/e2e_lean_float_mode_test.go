package compiler

import (
	"strings"
	"testing"
)

// -lean-floats bits (docs/spec/95-extraction.md section 3, "Seventh"): f32
// addition, subtraction, and multiplication render through Oak.FloatOps'
// bit-level operations, so a theorem reaches the rounding; the default
// keeps Lean's operators.
func TestE2ELeanFloatBitsMode(t *testing.T) {
	src := `package main

axpy: (a: f32, x: f32, y: f32): f32 = a * x + y
diff: (a: f32, b: f32): f32 = a - b
ratio: (a: f32, b: f32): f32 = a / b

main: (): i32 = 0
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	bits, err := New().WithPackageDir(root).WithLeanFloats("bits").EmitLeanRoots("Oak.Bits", []string{"axpy", "diff", "ratio"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"import Oak.FloatOps",
		"(Oak.FloatOps.add32 (Oak.FloatOps.mul32 a x) y)",
		"(Oak.FloatOps.sub32 a b)",
		"(a / b)",
	} {
		if !strings.Contains(bits, want) {
			t.Fatalf("missing %q in:\n%s", want, bits)
		}
	}
	plain, err := New().WithPackageDir(root).EmitLeanRoots("Oak.Plain", []string{"axpy"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(plain, "((a * x) + y)") || strings.Contains(plain, "FloatOps") {
		t.Fatalf("the default keeps Lean's operators:\n%s", plain)
	}
}
