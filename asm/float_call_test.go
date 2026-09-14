package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// A call to a program function with f32/f64 parameters and result is
// summarized like an integer one (docs/spec/94-assembler.md §8, floats):
// the arguments are read from the low lanes of v0–v7 (fa0–fa7 on RV64),
// the callee's body lowers as a float at its return width, and the result
// lands in the low lane of v0 (fa0). On the Oak side the call is a float
// of the callee's return width, so `-diff(a, b)` flips the sign bit.
func TestVerifyFloatCall(t *testing.T) {
	diff, err := parseSignatureWithBody("diff: (a, b: f32) -> f32 = a - b")
	if err != nil {
		t.Fatal(err)
	}
	decl := "neg_diff: (a, b: f32) -> f32"
	arm := func(t *testing.T, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n  bind s0 = a\n  bind s1 = b\n  clobber x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n  bl diff\n  fneg s0, s0\n  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = map[string]*ast.FunctionStatement{"diff": diff}
		if findings := Check(unit.Functions[0], sig, map[string]bool{"diff": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	proven := arm(t, "-diff(a, b)")
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "callees taken at their Oak bodies: diff") {
		t.Fatalf("-diff(a, b) against bl diff; fneg: want proven naming diff, got %s: %s", proven.Kind, proven.Message)
	}
	// The summary is the callee's body: the operand order and the
	// negation are both checked.
	if v := arm(t, "-diff(b, a)"); v.Kind != VerdictMismatch {
		t.Fatalf("-diff(b, a) must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := arm(t, "diff(a, b)"); v.Kind != VerdictMismatch {
		t.Fatalf("diff(a, b) without the negation must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	// A prefix operand carries its contract: -n is a signed 64-bit source
	// of the conversion.
	if v := verifyCase(t, "from_neg: (n: i64) -> f64", "f64_round_i64(-n)", "  bind x0 = n\n  neg x0, x0\n  scvtf d0, x0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64_round_i64(-n) against neg/scvtf must be proven, got %s: %s", v.Kind, v.Message)
	}
	if v := verifyCase(t, "from_neg: (n: i64) -> f64", "f64_round_i64(-n)", "  bind x0 = n\n  neg x0, x0\n  ucvtf d0, x0\n  ret"); v.Kind != VerdictMismatch {
		t.Fatalf("f64_round_i64(-n) against ucvtf must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}

// The RV64 lane: the arguments in fa0/fa1, the result in fa0.
func TestRV64VerifyFloatCall(t *testing.T) {
	diff, err := parseSignatureWithBody("diff: (a, b: f32) -> f32 = a - b")
	if err != nil {
		t.Fatal(err)
	}
	decl := "neg_diff: (a, b: f32) -> f32"
	rv := func(t *testing.T, oakBody string) Verdict {
		t.Helper()
		fn, errs := rv64Unit(t, decl, "  bind fa0 = a\n  bind fa1 = b\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call diff\n  fsgnjn.s fa0, fa0, fa0\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		fn.Callees = map[string]*ast.FunctionStatement{"diff": diff}
		if findings := Check(fn, sig, map[string]bool{"diff": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(fn, sig, spec.Body)
	}
	if v := rv(t, "-diff(a, b)"); v.Kind != VerdictProven || !strings.Contains(v.Message, "diff") {
		t.Fatalf("want proven naming diff, got %s: %s", v.Kind, v.Message)
	}
	if v := rv(t, "-diff(b, a)"); v.Kind != VerdictMismatch {
		t.Fatalf("-diff(b, a) must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
	if v := rv64Verify(t, "from_neg: (n: i64) -> f64", "f64_round_i64(-n)", "  bind a0 = n\n  sub a0, zero, a0\n  fcvt.d.l fa0, a0\n  ret"); v.Kind != VerdictProven {
		t.Fatalf("f64_round_i64(-n) against sub/fcvt.d.l must be proven, got %s: %s", v.Kind, v.Message)
	}
}
