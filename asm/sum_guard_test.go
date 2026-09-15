package asm

import (
	"strings"
	"testing"
)

// The sum shape of a slack guard (docs/spec/94-assembler.md §7;
// Oak.Assembler.sum_guard_slack): `len(v) >= i + K` lowers to `add wS, wI,
// #K; cmp wL, wS; b.lo <exit>`, and the fall-through knows wI + K <= len —
// so wI's element and the K - 1 after it (`add wJ, wI, #k`, k < K) are
// admitted without their own guards; the K-th is not.
func TestCheckSumGuardSlack(t *testing.T) {
	decl := "word_at: (v: []u8, i: u32) -> u32"
	body := "  bind x0, w1 = v\n  bind w2 = i\n  clobber x9, x10, x11\n  add w9, w2, #8\n  cmp w1, w9\n  b.lo done\n  ldrb w10, [x0, w2, uxtw]\n  add w11, w2, #7\n  ldrb w11, [x0, w11, uxtw]\n  add w10, w10, w11\n  mov w0, w10\n  ret\ndone:\n  mov w0, wzr\n  ret"
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("the elements under the sum guard must be admitted: %v", findings)
	}
	// The eighth element past the index is outside the guard.
	past := strings.Replace(body, "  add w11, w2, #7\n", "  add w11, w2, #8\n", 1)
	unit, errs = ParseUnit("v.oakasm", decl+" = {\n"+past+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) == 0 {
		t.Fatalf("the element at i + K must be refused")
	}
	// Without the branch the sum proves nothing.
	unguarded := strings.Replace(body, "  cmp w1, w9\n  b.lo done\n", "", 1)
	unit, errs = ParseUnit("v.oakasm", decl+" = {\n"+unguarded+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) == 0 {
		t.Fatalf("without the guard the accesses must be refused")
	}
}
