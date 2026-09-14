package asm

import (
	"strings"
	"testing"
)

// The length-equality fact (docs/spec/94-assembler.md §7; Oak.Assembler
// .index_under_equal_len): `cmp wLa, wLb; b.ne <exit>` proves the two spans'
// lengths equal on the fall-through path, so an index guarded below the
// first length is admitted into the second span too — the second span
// walked in step needs no guard of its own. Without the comparison the
// second access is refused.
func TestCheckIndexUnderEqualLength(t *testing.T) {
	decl := "dot_pair: (a: []u32, b: []u32) -> u32"
	body := "  bind x0, w1 = a\n  bind x2, w3 = b\n  clobber x9, x10, x11\n  cmp w1, w3\n  b.ne done\n  mov w9, wzr\nloop:\n  cmp w9, w1\n  b.hs done\n  ldr w10, [x0, w9, uxtw #2]\n  ldr w11, [x2, w9, uxtw #2]\n  add w10, w10, w11\n  add w9, w9, #1\n  b loop\ndone:\n  mov w0, w9\n  ret"
	unit, errs := ParseUnit("v.oakasm", decl+" = {\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(unit.Functions[0], sig, nil); len(findings) != 0 {
		t.Fatalf("the second span's access under the equality must be admitted: %v", findings)
	}
	// Without the equality the second access is guarded against the wrong length.
	unguarded := strings.Replace(body, "  cmp w1, w3\n  b.ne done\n", "", 1)
	unit, errs = ParseUnit("v.oakasm", decl+" = {\n"+unguarded+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	findings := Check(unit.Functions[0], sig, nil)
	if len(findings) == 0 || !strings.Contains(findings[0], "not this span's length register") {
		t.Fatalf("without the equality the second access must be refused, got %v", findings)
	}
}
