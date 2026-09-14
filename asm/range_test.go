package asm

import "testing"

// The term algebra's shift count wraps at the width (eval: l << (r %
// width)), so a fold that reads a shift by the width as zero, or a bound
// that does, is wrong: `y shl 32` at 32 bits is y.
func TestShiftCountWrapsAtWidth(t *testing.T) {
	x := paramTerm("x", 32)
	y := paramTerm("y", 32)
	wrapped := binaryTerm("or", x, binaryTerm("shl", y, constTerm(32, 32)))
	env := map[string]uint64{"x": 5, "y": 8}
	if got := truncate(wrapped, 32).eval(env); got != 13 {
		t.Fatalf("truncate(x | (y shl 32 at 32 bits), 32) must keep y (13), got %d", got)
	}
	if got := maxValue(binaryTerm("shl", constTerm(3, 32), constTerm(32, 32))); got < 3 {
		t.Fatalf("the bound of 3 shl 32 at 32 bits must be at least 3 (the count wraps), got %d", got)
	}
	// Above the width the shifted operand does vanish under a truncation.
	wide := binaryTerm("or", zeroExtend(x, 64), binaryTerm("shl", zeroExtend(y, 64), constTerm(32, 64)))
	if got := truncate(wide, 32).eval(env); got != 5 {
		t.Fatalf("truncate(zext x | (zext y shl 32 at 64 bits), 32) must be x (5), got %d", got)
	}
	if narrow := truncate(wide, 32); narrow.kind != termParam || narrow.name != "x" {
		t.Fatalf("the truncation must fold to the parameter x, got %s", narrow)
	}
}

// A float element of a local array, or a float field of a record local,
// compares at its own width: `out[1] == -1.0` reads the literal as an f32,
// not the f64 default (asm/floats_lowering.go floatWidthOf). Before the
// rule the Oak side compared f32 bits with f64 bits and refuted itself.
func TestFloatElementWidth(t *testing.T) {
	element := verifyCase(t, "tail_is_minus_one: (x: f32) -> u32", "{\n  a: [2]f32 = [2]f32{x, -1.0}\n  a[1] == -1.0 ? u32(1) | u32(0)\n}", "  bind s0 = x\n  mov w0, #1\n  ret")
	if element.Kind != VerdictProven {
		t.Fatalf("a local float array's element must compare at its width, got %s: %s", element.Kind, element.Message)
	}
}
