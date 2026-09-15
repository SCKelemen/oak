package asm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

// A loop site reached on several paths — a call to a looping callee after
// a diamond, here, with a count from either arm — is one loop event, its
// fields selected by the path taken (loopSite, mergeLoopEvents), as the
// Oak side's single event is; the two sides then pair by index and the
// coupling proves the caller. An arm passing the wrong count is refuted.
func TestVerifyLoopSitesAcrossPaths(t *testing.T) {
	sum, err := parseSignatureWithBody("sum_loop: (v: []u32, n: u32) -> u32 {\n  acc: u32 = u32(0)\n  i: u32 = u32(0)\n  while i < n {\n    acc = acc + v[i]\n    i = i + u32(1)\n  }\n  acc\n}")
	if err != nil {
		t.Fatal(err)
	}
	callees := map[string]*ast.FunctionStatement{"sum_loop": sum}
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
		unit.Functions[0].Callees = callees
		if findings := Check(unit.Functions[0], sig, map[string]bool{"sum_loop": true}); len(findings) != 0 {
			t.Fatalf("checker: %v", findings)
		}
		spec, err := parseSignatureWithBody(decl + " = " + oakBody)
		if err != nil {
			t.Fatal(err)
		}
		return Verify(unit.Functions[0], sig, spec.Body)
	}
	body := func(elseReg string) string {
		return "  bind x0, w1 = v\n  bind w2 = n\n  bind w3 = k\n  clobber x9, x29, x30\n  frame 16\n  sub sp, sp, #16\n  stp x29, x30, [sp]\n  cmp w3, #4\n  b.hs else_1\n  mov w9, w2\n  b endif_1\nelse_1:\n  mov w9, " + elseReg + "\nendif_1:\n  mov w2, w9\n  bl sum_loop\n  add w0, w0, #1\n  ldp x29, x30, [sp]\n  add sp, sp, #16\n  ret"
	}
	oak := "{\n  m: u32 = k < u32(4) ? { n } | { k }\n  sum_loop(v, m) + u32(1)\n}"
	good := pair(t, "sum_sel: (v: []u32, n: u32, k: u32) -> u32", body("w3"), oak)
	if good.Kind != VerdictProven || !strings.Contains(good.Message, "coupled inductively") {
		t.Fatalf("a looping callee reached on two paths must be one event and proven, got %s: %s", good.Kind, good.Message)
	}
	// The else arm passes n where the Oak body passes k: refuted.
	wrong := pair(t, "sum_sel_n: (v: []u32, n: u32, k: u32) -> u32", body("w2"), oak)
	if wrong.Kind != VerdictMismatch {
		t.Fatalf("a wrong count on one arm must be refuted, got %s: %s", wrong.Kind, wrong.Message)
	}
}
