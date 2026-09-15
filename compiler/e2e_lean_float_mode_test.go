package compiler

import (
	"strings"
	"testing"
)

// -lean-floats bits (docs/spec/95-extraction.md section 3, "Seventh"): f32
// arithmetic, sign operations, and comparisons render through Oak.FloatOps'
// bit-level operations, so a theorem reaches the rounding, exact bit changes,
// and IEEE predicates; the default keeps Lean's operators.
func TestE2ELeanFloatBitsMode(t *testing.T) {
	src := `package main

axpy: (a: f32, x: f32, y: f32): f32 = a * x + y
diff: (a: f32, b: f32): f32 = a - b
ratio: (a: f32, b: f32): f32 = a / b
signed: (x: f32, y: f32): f32 = copysign(abs(-x), y)
eq: (a: f32, b: f32): Bool = a == b
ne: (a: f32, b: f32): Bool = a != b
lt: (a: f32, b: f32): Bool = a < b
le: (a: f32, b: f32): Bool = a <= b
gt: (a: f32, b: f32): Bool = a > b
ge: (a: f32, b: f32): Bool = a >= b
lt64: (a: f64, b: f64): Bool = a < b

main: (): i32 = 0
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	bits, err := New().WithPackageDir(root).WithLeanFloats("bits").EmitLeanRoots("Oak.Bits", []string{"axpy", "diff", "ratio", "signed", "eq", "ne", "lt", "le", "gt", "ge", "lt64"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"import Oak.FloatOps",
		"(Oak.FloatOps.add32 (Oak.FloatOps.mul32 a x) y)",
		"(Oak.FloatOps.sub32 a b)",
		"(a / b)",
		"(Oak.FloatOps.copysign32 (Oak.FloatOps.abs32 (Oak.FloatOps.neg32 x)) y)",
		"(Oak.FloatOps.eq32 a b)",
		"(Oak.FloatOps.ne32 a b)",
		"(Oak.FloatOps.lt32 a b)",
		"(Oak.FloatOps.le32 a b)",
		"(Oak.FloatOps.gt32 a b)",
		"(Oak.FloatOps.ge32 a b)",
		"(decide (a < b))",
	} {
		if !strings.Contains(bits, want) {
			t.Fatalf("missing %q in:\n%s", want, bits)
		}
	}
	plain, err := New().WithPackageDir(root).EmitLeanRoots("Oak.Plain", []string{"axpy", "eq"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(plain, "((a * x) + y)") || !strings.Contains(plain, "(a == b)") || strings.Contains(plain, "FloatOps") {
		t.Fatalf("the default keeps Lean's operators:\n%s", plain)
	}
	plainSigned, err := New().WithPackageDir(root).EmitLeanRoots("Oak.PlainSigned", []string{"signed"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(plainSigned, "(Oak.FloatOps.copysign32 (Float32.abs (-x)) y)") ||
		strings.Contains(plainSigned, "FloatOps.neg32") || strings.Contains(plainSigned, "FloatOps.abs32") {
		t.Fatalf("the default keeps Lean's unary operators:\n%s", plainSigned)
	}
}
