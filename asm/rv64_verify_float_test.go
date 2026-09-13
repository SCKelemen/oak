package asm

import (
	"strings"
	"testing"
)

// The RV64 lane's floating-point instructions verified against the Oak
// body up to the IEEE operations (docs/spec/94-assembler.md §8, §9): the
// same verdicts the AArch64 lane gives, through the F/D mnemonics.
func TestRV64VerifyFloat(t *testing.T) {
	decl := "axpy: (a, x, y: f64) -> f64"
	bind := "  bind fa0 = a\n  bind fa1 = x\n  bind fa2 = y\n"
	if v := rv64Verify(t, decl, "fma(a, x, y)", bind+"  fmadd.d fa0, fa0, fa1, fa2\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("fma against fmadd.d must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "a * x + y", bind+"  fmadd.d fa0, fa0, fa1, fa2\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("contracting a*x + y into fmadd.d must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "a * x + y", bind+"  fmul.d fa0, fa0, fa1\n  fadd.d fa0, fa0, fa2\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("fmul.d then fadd.d must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "fma(-a, x, -y)", bind+"  fnmadd.d fa0, fa0, fa1, fa2\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("fnmadd.d as fma(-a, x, -y) must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, decl, "a * x + y", bind+"  fmul.d fa0, fa0, fa1, rtz\n  fadd.d fa0, fa0, fa2\n  ret"); v.Kind != VerdictTrusted || !strings.Contains(v.Message, "static rounding mode") {
		t.Fatalf("a static rounding mode must leave the unit trusted, got %s: %s", v.Kind, v.Message)
	}
	// RISC-V fmin is minimumNumber: Oak's min_num, not its min.
	two := "  bind fa0 = a\n  bind fa1 = b\n"
	if v := rv64Verify(t, "least: (a, b: f32) -> f32", "min_num(a, b)", two+"  fmin.s fa0, fa0, fa1\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("min_num against fmin.s must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "least: (a, b: f32) -> f32", "min(a, b)", two+"  fmin.s fa0, fa0, fa1\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("min against fmin.s (a NaN operand suppressed) must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Sign injection: neg, abs, and copysign are fsgnj forms.
	if v := rv64Verify(t, "root: (x: f64) -> f64", "sqrt(abs(-x))", "  bind fa0 = x\n  fsgnjn.d fa0, fa0, fa0\n  fsgnjx.d fa0, fa0, fa0\n  fsqrt.d fa0, fa0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("sqrt(abs(-x)) through fsgnj forms must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "sign: (a, b: f64) -> f64", "copysign(a, b)", two+"  fsgnj.d fa0, fa0, fa1\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("copysign against fsgnj.d must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Comparisons into the integer file, and a select built from one.
	if v := rv64Verify(t, "less: (a, b: f64) -> Bool", "a < b", two+"  flt.d a0, fa0, fa1\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("a < b against flt.d must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "less: (a, b: f64) -> Bool", "a <= b", two+"  flt.d a0, fa0, fa1\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("a <= b against flt.d must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// Conversions: an integer to a float, a float to an integer toward
	// zero (rtz spelled), and a width change.
	if v := rv64Verify(t, "to_f32: (n: u32) -> f32", "f32(n)", "  bind a0 = n\n  fcvt.s.wu fa0, a0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f32(n) against fcvt.s.wu must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "to_f32: (n: u32) -> f32", "f32(n)", "  bind a0 = n\n  fcvt.s.w fa0, a0\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("f32(n) against fcvt.s.w must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "trunc_u: (x: f64) -> u64", "u64(x)", "  bind fa0 = x\n  fcvt.lu.d a0, fa0, rtz\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("u64(x) against fcvt.lu.d rtz must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "trunc_u: (x: f64) -> u64", "u64(x)", "  bind fa0 = x\n  fcvt.lu.d a0, fa0\n  ret"); v.Kind != VerdictTrusted {
		t.Fatalf("a float-to-integer conversion without rtz must stay trusted, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "widen: (x: f32) -> f64", "f64(x)", "  bind fa0 = x\n  fcvt.d.s fa0, fa0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64(x) against fcvt.d.s must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Bits across the files: a constant through fmv.d.x, and u64_bits_f64.
	if v := rv64Verify(t, "twice: (x: f64) -> f64", "x * 2.0", "  bind fa0 = x\n  clobber t0, ft0\n  li t0, 1\n  slli t0, t0, 62\n  fmv.d.x ft0, t0\n  fmul.d fa0, fa0, ft0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("x * 2.0 through fmv.d.x must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "bits: (x: f32) -> u32", "u32_bits_f32(x)", "  bind fa0 = x\n  fmv.x.w a0, fa0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("u32_bits_f32 against fmv.x.w must be proven, got %s: %s", v.Kind, v.Message)
	}
	// A float through the frame: stored and reloaded.
	if v := rv64Verify(t, "same: (x: f64) -> f64", "x", "  bind fa0 = x\n  frame 16\n  addi sp, sp, -16\n  fsd fa0, 8(sp)\n  fld fa0, 8(sp)\n  addi sp, sp, 16\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("a float round-tripped through the frame must be proven, got %s: %s", v.Kind, v.Message)
	}
}
