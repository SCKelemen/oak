package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// Views over aggregates (docs/spec/94-assembler.md §8, views over
// aggregates): a span local over an owned array is the array at an
// offset — reads, writes, `len`, and a callee's parameter bound to it all
// translate to the array — so a body naming such views is proven against
// the same machine code as one indexing the array directly.
func TestVerifyAggregateViews(t *testing.T) {
	put, err := parseSignatureWithBody("put: (v: [*]u32, i: u32, x: u32) -> () {\n  v[i] = x\n}")
	if err != nil {
		t.Fatal(err)
	}
	pair := func(t *testing.T, decl, asmBody, oakBody string) Verdict {
		t.Helper()
		unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+asmBody+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		unit.Functions[0].Callees = map[string]*ast.FunctionStatement{"put": put}
		if findings := Check(unit.Functions[0], sig, map[string]bool{"put": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	// The machine: a zero-filled two-element array at [sp, #16], put(span, 1, x), the element read back.
	asmBody := "  bind w0 = x\n  clobber x0, x1, x2, x3, x9, x19, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  str x19, [sp, #32]\n  mov w19, w0\n  str xzr, [sp, #16]\n  add x0, sp, #16\n  movz w1, #2\n  movz w2, #1\n  mov w3, w19\n  bl put\n  ldr w0, [sp, #20]\n  ldr x19, [sp, #32]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret"
	// The Oak body through a view local: the whole array, passed on and read back.
	whole := "{\n  buf: [2]u32\n  w: [*]u32 = span(&buf)\n  put(w, u32(1), x)\n  w[1]\n}"
	if v := pair(t, "set_one: (x: u32) -> u32", asmBody, whole); v.Kind != VerdictProven {
		t.Fatalf("a view over the whole array must be proven, got %s: %s", v.Kind, v.Message)
	}
	// Through a subslice view: element 0 of the tail is the array's element 1.
	tail := "{\n  buf: [2]u32\n  w: [*]u32 = span(&buf)\n  put(w, u32(1), x)\n  t: []u32 = subslice(w, u32(1), u32(1))\n  t[0] + u32(0) * len(t)\n}"
	if v := pair(t, "set_one: (x: u32) -> u32", asmBody, tail); v.Kind != VerdictProven {
		t.Fatalf("a subslice view must read the array at its offset, got %s: %s", v.Kind, v.Message)
	}
	// The wrong offset is refuted.
	head := "{\n  buf: [2]u32\n  w: [*]u32 = span(&buf)\n  put(w, u32(1), x)\n  t: []u32 = subslice(w, u32(0), u32(1))\n  t[0]\n}"
	if v := pair(t, "set_one: (x: u32) -> u32", asmBody, head); v.Kind != VerdictMismatch {
		t.Fatalf("a subslice view at the wrong offset must be a mismatch, got %s: %s", v.Kind, v.Message)
	}
}
