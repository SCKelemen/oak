package asm

import (
	"strings"
	"testing"
)

// The index guards the checker carries past a copy, a slack compare, and a
// call — the admissions that let the native lowering elide the guards the
// typechecker proved (docs/spec/94-assembler.md §9, "Proof-guided
// elision"); each cites its law.
func TestCheckerGuardFacts(t *testing.T) {
	decl := "read: (v: []u8, i: u32) -> u32"
	symbols := map[string]bool{"helper": true}
	epilogue := "\ntrap:\n  brk #1"
	// A body that calls: the span parked in x19/w20, the index in w21.
	callPrologue := "  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x19, x20, x21, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  stp x19, x20, [sp, #16]\n  str x21, [sp, #32]\n  mov x19, x0\n  mov w20, w1\n  mov w21, w2\n"
	callEpilogue := "\n  ldr x21, [sp, #32]\n  ldp x19, x20, [sp, #16]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret" + epilogue
	accepts := []struct{ name, body string }{
		{"add #0 carries the guard (Oak.SpanAlias.idxMeans_preserved)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add w9, w2, #0\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue},
		{"exclusive slack guard admits the reads before the slack (Oak.Assembler.slack_guard_strict)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #4\n  b.lo trap\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #3\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue},
		{"guard on callee-saved registers survives a call",
			callPrologue + "  cmp w21, w20\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]" + callEpilogue},
		{"guard against the caller-saved length rebinds to its callee-saved copy",
			callPrologue + "  cmp w21, w1\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]" + callEpilogue},
		{"proven minimum survives a call with the span",
			callPrologue + "  cmp w20, #2\n  b.lo trap\n  bl helper\n  ldrb w0, [x19, #1]" + callEpilogue},
	}
	for _, tc := range accepts {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("guard.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			if findings := Check(unit.Functions[0], sig, symbols); len(findings) != 0 {
				t.Fatalf("must pass: %v", findings)
			}
		})
	}
	rejects := []struct{ name, body, want string }{
		{"add #1 does not carry a plain guard",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  cmp w2, w1\n  b.hs trap\n  add w9, w2, #1\n  ldrb w0, [x0, w9, uxtw]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"exclusive slack guard does not reach the element at the slack",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  cmp w1, #4\n  b.lo trap\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #4\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue,
			"without a dominating index guard"},
		{"slack guard without the minimum proven (the subtraction may wrap)",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hs trap\n  add w10, w2, #3\n  ldrb w0, [x0, w10, uxtw]\n  ret" + epilogue,
			"len >= 4 proven first"},
		{"inclusive slack guard without the minimum proven, scalar read",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9\n  mov w9, w1\n  sub w9, w9, #4\n  cmp w2, w9\n  b.hi trap\n  ldrb w0, [x0, w2, uxtw]\n  ret" + epilogue,
			"len >= 4 proven first"},
		{"guard on a caller-saved index dies at a call",
			callPrologue + "  mov w9, w21\n  cmp w9, w20\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w9, uxtw]" + callEpilogue,
			"without a dominating index guard"},
		{"guard against a length with no callee-saved copy dies at a call",
			"  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x19, x21, x29, x30\n  frame 48\n  sub sp, sp, #48\n  stp x29, x30, [sp]\n  stp x19, x21, [sp, #16]\n  mov x19, x0\n  mov w21, w2\n  cmp w21, w1\n  b.hs trap\n  bl helper\n  ldrb w0, [x19, w21, uxtw]\n  ldp x19, x21, [sp, #16]\n  ldp x29, x30, [sp]\n  add sp, sp, #48\n  ret" + epilogue,
			""},
	}
	for _, tc := range rejects {
		t.Run(tc.name, func(t *testing.T) {
			unit, errs := ParseUnit("guard.oakasm", decl+" = {\n"+tc.body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, _ := parseSignature(decl)
			joined := strings.Join(Check(unit.Functions[0], sig, symbols), "\n")
			if joined == "" || !strings.Contains(joined, tc.want) {
				t.Fatalf("expected a finding mentioning %q, got:\n%s", tc.want, joined)
			}
		})
	}
}
