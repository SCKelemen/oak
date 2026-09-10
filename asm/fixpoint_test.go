package asm

import (
	"strings"
	"testing"
)

func checkBody(t *testing.T, decl, body string) []string {
	t.Helper()
	unit, errs := ParseUnit("f.oakasm", decl+" = {\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	return Check(unit.Functions[0], sig, nil)
}

// Guard facts across labels (docs/spec/94-assembler.md §7): a label holds
// exactly the facts every predecessor carries — fall-through and every
// branch, forward or backward — computed as a fixpoint over the passes.
func TestGuardFixpoint(t *testing.T) {
	decl := "sum4: (v: []u32) -> u32"
	// The idiom: one length guard before the loop; the loop header is
	// reached by fall-through (len >= 4 held) and by the back edge (still
	// held), so the constant-bound index guard inside composes with it.
	outerGuard := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  cmp w1, #4\n  b.lo short\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, #4\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret\nshort:\n  mov w0, #0\n  ret"
	if findings := checkBody(t, decl, outerGuard); len(findings) != 0 {
		t.Fatalf("the outer guard must survive the loop header: %v", findings)
	}
	// Writing the length register on the back edge kills the fact at the
	// header: the merge of (len >= 4) with (nothing) is nothing.
	killed := strings.Replace(outerGuard, "  add w9, w9, #1\n", "  add w9, w9, #1\n  add w1, w1, #0\n", 1)
	findings := checkBody(t, decl, killed)
	if len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "proven minimum length is 0") {
		t.Fatalf("a back edge without the fact must drop it at the header, got: %v", findings)
	}
	// Two predecessors with different bounds meet at the smaller one.
	meet := "  bind x0, w1 = v\n  bind w2 = pick\n  cmp w2, #0\n  b.eq wide\n  cmp w1, #2\n  b.lo short\n  b join\nwide:\n  cmp w1, #8\n  b.lo short\njoin:\n  ldr w0, [x0, #4]\n  ret\nshort:\n  mov w0, #0\n  ret"
	if findings := checkBody(t, "second: (v: []u32, pick: u32) -> u32", meet); len(findings) != 0 {
		t.Fatalf("offset 4 is inside the smaller proven length (2 elements): %v", findings)
	}
	tooFar := strings.Replace(meet, "ldr w0, [x0, #4]", "ldr w0, [x0, #28]", 1)
	findings = checkBody(t, "second: (v: []u32, pick: u32) -> u32", tooFar)
	if len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "proves only 2 elements") {
		t.Fatalf("offset 28 needs 8 elements but the merge proves 2, got: %v", findings)
	}
	// A label reached only by a branch from before the guard holds nothing.
	early := "  bind x0, w1 = v\n  bind w2 = pick\n  cmp w2, #0\n  b.eq body\n  cmp w1, #2\n  b.lo short\nbody:\n  ldr w0, [x0]\n  ret\nshort:\n  mov w0, #0\n  ret"
	findings = checkBody(t, "second: (v: []u32, pick: u32) -> u32", early)
	if len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "without a dominating bounds guard") {
		t.Fatalf("an unguarded predecessor must drop the fact, got: %v", findings)
	}
}

// With the outer guard surviving the header, the sum loop verifies in its
// idiomatic form: one length check, then the counted walk.
func TestVerifyOuterGuardLoop(t *testing.T) {
	decl := "sum4: (v: []u32) -> u32"
	outerGuard := "  bind x0, w1 = v\n  clobber w9, w10, w11\n  cmp w1, #4\n  b.lo short\n  mov w9, #0\n  mov w10, #0\nloop:\n  cmp w9, #4\n  b.hs done\n  ldr w11, [x0, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w10\n  ret\nshort:\n  mov w0, #0\n  ret"
	oakLoop := "{\n  len(v) < u32(4) ? { u32(0) } | {\n    acc: u32 = u32(0)\n    i: u32 = u32(0)\n    while i < u32(4) {\n      acc = acc + v[i]\n      i = i + u32(1)\n    }\n    acc\n  }\n}"
	proven := verifyCase(t, decl, oakLoop, outerGuard)
	if proven.Kind != VerdictProven {
		t.Fatalf("the idiomatic sum loop must be proven, got %s: %s", proven.Kind, proven.Message)
	}
}
