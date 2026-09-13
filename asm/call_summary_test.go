package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// Call summaries (docs/spec/94-assembler.md §8): a call to a program
// function with a scalar signature is taken at the callee's Oak body, so a
// caller is proven rather than trusted, relative to the callee's own
// verdict; the verdict names the callees so taken. Without the program's
// functions, or with a callee outside the scalar contract, the call stays
// opaque and the function trusted with the reason.
func TestVerifyCallSummary(t *testing.T) {
	inc, err := parseSignatureWithBody("inc: (a: u32) -> u32 = a + u32(1)")
	if err != nil {
		t.Fatal(err)
	}
	fill, err := parseSignatureWithBody("fill: (v: [*]u8, i: u32) -> u32 { v[0] = u8(1)\n i }")
	if err != nil {
		t.Fatal(err)
	}
	arm := func(t *testing.T, callees map[string]*ast.FunctionStatement, oakBody string) Verdict {
		t.Helper()
		decl := "twice: (a: u32) -> u32"
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n  bind w0 = a\n  clobber x9, x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n  bl inc\n  mov w9, w0\n  add w0, w9, w9\n  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = callees
		if findings := Check(unit.Functions[0], sig, map[string]bool{"inc": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	proven := arm(t, map[string]*ast.FunctionStatement{"inc": inc}, "inc(a) + inc(a)")
	if proven.Kind != VerdictProven || !strings.Contains(proven.Message, "callees taken at their Oak bodies: inc") {
		t.Fatalf("with the callee known: want proven naming inc, got %s: %s", proven.Kind, proven.Message)
	}
	// The summary is the callee's body, not a guess: a caller claiming
	// three increments is refuted.
	refuted := arm(t, map[string]*ast.FunctionStatement{"inc": inc}, "inc(a) + inc(a) + u32(1)")
	if refuted.Kind != VerdictMismatch {
		t.Fatalf("a wrong Oak body must be refuted, got %s: %s", refuted.Kind, refuted.Message)
	}
	opaque := arm(t, nil, "inc(a) + inc(a)")
	if opaque.Kind != VerdictTrusted || !strings.Contains(opaque.Message, "instruction bl") {
		t.Fatalf("without callees the call stays opaque, got %s: %s", opaque.Kind, opaque.Message)
	}
	spanned := arm(t, map[string]*ast.FunctionStatement{"inc": fill}, "inc(a) + inc(a)")
	if spanned.Kind != VerdictTrusted || !strings.Contains(spanned.Message, "not a fixed-width integer") {
		t.Fatalf("a span parameter is outside the summary, got %s: %s", spanned.Kind, spanned.Message)
	}
}

// The RV64 lane: the summary widens the result as the psABI does.
func TestVerifyCallSummaryRV64(t *testing.T) {
	inc, err := parseSignatureWithBody("inc: (a: u32) -> u32 = a + u32(1)")
	if err != nil {
		t.Fatal(err)
	}
	decl := "twice: (a: u32) -> u32"
	unit, errs := ParseUnit("v.rv64.oakasm", decl+" = {\n  bind a0 = a\n  clobber t0\n  frame 16\n  addi sp, sp, -16\n  sd ra, 8(sp)\n  call inc\n  mv t0, a0\n  addw a0, t0, t0\n  ld ra, 8(sp)\n  addi sp, sp, 16\n  ret\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	unit.Functions[0].Callees = map[string]*ast.FunctionStatement{"inc": inc}
	if findings := Check(unit.Functions[0], sig, map[string]bool{"inc": true}); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = inc(a) + inc(a)")
	if err != nil {
		t.Fatal(err)
	}
	verdict := Verify(unit.Functions[0], sig, spec.Body)
	if verdict.Kind != VerdictProven || !strings.Contains(verdict.Message, "inc") {
		t.Fatalf("want proven naming inc, got %s: %s", verdict.Kind, verdict.Message)
	}
}
