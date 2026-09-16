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

func TestMergeLoopEventsKeepsOneStructurallyEqualWriteLog(t *testing.T) {
	event := func(value uint64) *loopEvent {
		return &loopEvent{
			index:   1,
			header:  map[string]*term{},
			fresh:   map[string]*term{},
			width:   map[string]int{},
			next:    map[string]*term{},
			cond:    paramTerm("loop1.cond", 1),
			reached: paramTerm("reached", 1),
			writes: map[string][]*spanWrite{
				"s.pages": {{index: paramTerm("loop1.j", 32), value: constTerm(value, 64), guard: paramTerm("ok", 1)}},
			},
		}
	}
	path := paramTerm("path", 1)
	merged, reason, ok := mergeLoopEvents(path, event(0), event(0))
	if !ok {
		t.Fatalf("equal events did not merge: %s", reason)
	}
	if got := len(merged.writes["s.pages"]); got != 1 {
		t.Fatalf("structurally equal stores must stay one operation, got %d", got)
	}
	if !equalTerms(merged.writes["s.pages"][0].guard, paramTerm("ok", 1)) {
		t.Fatalf("the callee-internal guard must be retained without a caller-path wrapper, got %s", merged.writes["s.pages"][0].guard)
	}

	different, reason, ok := mergeLoopEvents(path, event(0), event(1))
	if !ok {
		t.Fatalf("different events did not merge conservatively: %s", reason)
	}
	if got := len(different.writes["s.pages"]); got != 2 {
		t.Fatalf("different stores must retain both guarded path operations, got %d", got)
	}
}

// A counted loop past the trip limit is summarized and inducted rather
// than unrolled, loop inside or not (countedTripLimit): the copy of a
// table's two thousand words unrolls into a write log no decision
// affords, where the induction over one iteration proves it in a few
// steps. A wrong store is refuted either way: in the inducted loop of
// eighty trips on a witness input long enough to run it (the witness
// lengths reach eighty-one), in an unrolled loop of forty by the same.
func TestVerifyLongCountedLoopInducted(t *testing.T) {
	body := func(trips string) string {
		return "  bind x0, w1 = v\n  bind w2 = x\n  clobber x9, x10\n  mov w9, wzr\nloop:\n  cmp w9, #" + trips + "\n  b.hs done\n  cmp w9, w1\n  b.hs trap\n  str w2, [x0, w9, uxtw #2]\n  add w9, w9, #1\n  b loop\ndone:\n  ret\ntrap:\n  brk #1"
	}
	oak := func(trips, value string) string {
		return "{\n  i: u32 = u32(0)\n  while i < u32(" + trips + ") {\n    v[i] = " + value + "\n    i = i + u32(1)\n  }\n}"
	}
	inducted := verifyCase(t, "fill80: (v: [*]u32, x: u32) -> ()", oak("80", "x"), body("80"))
	if inducted.Kind != VerdictProven || !strings.Contains(inducted.Message, "coupled inductively") {
		t.Fatalf("a long counted store loop must be inducted and proven, got %s: %s", inducted.Kind, inducted.Message)
	}
	if wrong := verifyCase(t, "fill80: (v: [*]u32, x: u32) -> ()", oak("80", "x + u32(1)"), body("80")); wrong.Kind != VerdictMismatch {
		t.Fatalf("a wrong store in an inducted loop must be refuted on a witness input, got %s: %s", wrong.Kind, wrong.Message)
	}
	unrolled := verifyCase(t, "fill40: (v: [*]u32, x: u32) -> ()", oak("40", "x"), body("40"))
	if unrolled.Kind != VerdictProven || strings.Contains(unrolled.Message, "coupled inductively") {
		t.Fatalf("a forty-trip loop unrolls and is proven, got %s: %s", unrolled.Kind, unrolled.Message)
	}
	if wrong := verifyCase(t, "fill40: (v: [*]u32, x: u32) -> ()", oak("40", "x + u32(1)"), body("40")); wrong.Kind != VerdictMismatch {
		t.Fatalf("a wrong store in an unrolled loop must be refuted, got %s: %s", wrong.Kind, wrong.Message)
	}
}
