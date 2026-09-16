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
widen: (a: f32, b: f32): f64 = f64(a + b)
mixed: (a: f32, b: f32, x: f64, y: f64): f64 = fma(f64(a + b), x, y)
mixed_arithmetic: (a: f32, b: f32, x: f64, y: f64): f64 = f64(a + b) * x + y
signed: (x: f32, y: f32): f32 = copysign(abs(-x), y)
signed64: (x: f64, y: f64): f64 = copysign(abs(-x), y)
eq: (a: f32, b: f32): Bool = a == b
ne: (a: f32, b: f32): Bool = a != b
lt: (a: f32, b: f32): Bool = a < b
le: (a: f32, b: f32): Bool = a <= b
gt: (a: f32, b: f32): Bool = a > b
ge: (a: f32, b: f32): Bool = a >= b
eq64: (a: f64, b: f64): Bool = a == b
ne64: (a: f64, b: f64): Bool = a != b
lt64: (a: f64, b: f64): Bool = a < b
le64: (a: f64, b: f64): Bool = a <= b
gt64: (a: f64, b: f64): Bool = a > b
ge64: (a: f64, b: f64): Bool = a >= b
guard64: (a: f64, b: f64): Bool = !(a < b) || a == b && b != a
choose64: (a: f64, b: f64): f64 = a < b ? -abs(a) | copysign(b, a)
nested64: (a: f64, b: f64): f64 = a < b ? (a == b ? -abs(a) | a + b) | copysign(b, a)
choose: (a: f32, b: f32): f32 = a < b ? a + 1.0 | b * 2.0
scale: (x: f32, y: f32): f32 = x * y + 1.0
via_call: (a: f32, b: f32): f32 = scale(a + b, b)
guard: (a: f32, b: f32): Bool = !(a < b) || a == b && b != 0.0
nested: (a: f32, b: f32): f32 = a < b ? (a == 0.0 ? a + 1.0 | b - 1.0) | b * 2.0
assigned: (a: f32, b: f32): f32 = {
  y: f32 = a
  a < b ? { y = b + 1.0 } | { y = a * 2.0 }
  y - 3.0
}
assigned_pair: (a: f32, b: f32): f32 = {
  x: f32 = a
  y: f32 = b
  x < y ? {
    x = y + 1.0
    y = x * 2.0
  } | {
    x = x - 1.0
    y = y + 3.0
  }
  x - y
}

main: (): i32 = 0
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	bits, err := New().WithPackageDir(root).WithLeanFloats("bits").EmitLeanRoots("Oak.Bits", []string{"axpy", "diff", "ratio", "widen", "mixed", "mixed_arithmetic", "signed", "signed64", "eq", "ne", "lt", "le", "gt", "ge", "eq64", "ne64", "lt64", "le64", "gt64", "ge64", "guard64", "choose64", "nested64", "choose", "via_call", "guard", "nested", "assigned", "assigned_pair"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"import Oak.FloatOps",
		"(Oak.FloatOps.add32 (Oak.FloatOps.mul32 a x) y)",
		"(Oak.FloatOps.sub32 a b)",
		"(a / b)",
		"((Oak.FloatOps.add32 a b).toFloat)",
		"(Oak.FloatOps.fma64 ((Oak.FloatOps.add32 a b).toFloat) x y)",
		"((((Oak.FloatOps.add32 a b).toFloat) * x) + y)",
		"(Oak.FloatOps.copysign32 (Oak.FloatOps.abs32 (Oak.FloatOps.neg32 x)) y)",
		"(Oak.FloatOps.copysign64 (Float.abs (-x)) y)",
		"(Oak.FloatOps.eq32 a b)",
		"(Oak.FloatOps.ne32 a b)",
		"(Oak.FloatOps.lt32 a b)",
		"(Oak.FloatOps.le32 a b)",
		"(Oak.FloatOps.gt32 a b)",
		"(Oak.FloatOps.ge32 a b)",
		"(a == b)",
		"(a != b)",
		"(decide (a < b))",
		"(decide (a <= b))",
		"(decide (a > b))",
		"(decide (a >= b))",
		"((!(decide (a < b))) || ((a == b) && (b != a)))",
		"(if (decide (a < b)) then (-(Float.abs a)) else (Oak.FloatOps.copysign64 b a))",
		"(if (decide (a < b)) then (if (a == b) then (-(Float.abs a)) else (a + b)) else (Oak.FloatOps.copysign64 b a))",
		"(if (Oak.FloatOps.lt32 a b) then (Oak.FloatOps.add32 a (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/)) else (Oak.FloatOps.mul32 b (Float32.ofBits (0x40000000 : UInt32) /- 2.0 -/)))",
		"def scale",
		"(Oak.FloatOps.add32 (Oak.FloatOps.mul32 x y) (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/))",
		"scale (Oak.FloatOps.add32 a b) b fuel",
		"((!(Oak.FloatOps.lt32 a b)) || ((Oak.FloatOps.eq32 a b) && (Oak.FloatOps.ne32 b (Float32.ofBits (0x00000000 : UInt32) /- 0.0 -/))))",
		"(if (Oak.FloatOps.lt32 a b) then (if (Oak.FloatOps.eq32 a (Float32.ofBits (0x00000000 : UInt32) /- 0.0 -/)) then (Oak.FloatOps.add32 a (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/)) else (Oak.FloatOps.sub32 b (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/))) else (Oak.FloatOps.mul32 b (Float32.ofBits (0x40000000 : UInt32) /- 2.0 -/)))",
		"let y ← (if (Oak.FloatOps.lt32 a b) then (do",
		"let y := (Oak.FloatOps.add32 b (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/))",
		"let y := (Oak.FloatOps.mul32 a (Float32.ofBits (0x40000000 : UInt32) /- 2.0 -/))",
		"pure (Oak.FloatOps.sub32 y (Float32.ofBits (0x40400000 : UInt32) /- 3.0 -/))",
		"let (x, y) ← (if (Oak.FloatOps.lt32 x y) then (do",
		"let x := (Oak.FloatOps.add32 y (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/))",
		"let y := (Oak.FloatOps.mul32 x (Float32.ofBits (0x40000000 : UInt32) /- 2.0 -/))",
		"let x := (Oak.FloatOps.sub32 x (Float32.ofBits (0x3F800000 : UInt32) /- 1.0 -/))",
		"let y := (Oak.FloatOps.add32 y (Float32.ofBits (0x40400000 : UInt32) /- 3.0 -/))",
		"pure (Oak.FloatOps.sub32 x y)",
	} {
		if !strings.Contains(bits, want) {
			t.Fatalf("missing %q in:\n%s", want, bits)
		}
	}
	plain, err := New().WithPackageDir(root).EmitLeanRoots("Oak.Plain", []string{"axpy", "mixed_arithmetic", "eq", "choose", "via_call", "guard", "nested", "assigned", "assigned_pair"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(plain, "((a * x) + y)") ||
		!strings.Contains(plain, "((((a + b).toFloat) * x) + y)") ||
		!strings.Contains(plain, "(a == b)") ||
		!strings.Contains(plain, "(if (decide (a < b)) then (a +") ||
		strings.Contains(plain, "FloatOps") {
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
	plain64, err := New().WithPackageDir(root).EmitLeanRoots("Oak.Plain64", []string{"signed64", "eq64", "ne64", "lt64", "le64", "gt64", "ge64", "guard64", "choose64", "nested64"}).Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"(Oak.FloatOps.copysign64 (Float.abs (-x)) y)",
		"(a == b)",
		"(a != b)",
		"(decide (a < b))",
		"(decide (a <= b))",
		"(decide (a > b))",
		"(decide (a >= b))",
		"((!(decide (a < b))) || ((a == b) && (b != a)))",
		"(if (decide (a < b)) then (-(Float.abs a)) else (Oak.FloatOps.copysign64 b a))",
		"(if (decide (a < b)) then (if (a == b) then (-(Float.abs a)) else (a + b)) else (Oak.FloatOps.copysign64 b a))",
	} {
		if !strings.Contains(plain64, want) {
			t.Fatalf("default binary64 extraction missing %q in:\n%s", want, plain64)
		}
	}
	if strings.Contains(plain64, "FloatOps.neg32") ||
		strings.Contains(plain64, "FloatOps.abs32") ||
		strings.Contains(plain64, "FloatOps.eq32") ||
		strings.Contains(plain64, "FloatOps.ne32") ||
		strings.Contains(plain64, "FloatOps.lt32") ||
		strings.Contains(plain64, "FloatOps.le32") ||
		strings.Contains(plain64, "FloatOps.gt32") ||
		strings.Contains(plain64, "FloatOps.ge32") {
		t.Fatalf("binary64 extraction used a binary32 carrier:\n%s", plain64)
	}
}
