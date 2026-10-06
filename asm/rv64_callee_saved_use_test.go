package asm

import (
	"strings"
	"testing"
)

// A saved callee-saved register may be used (docs/spec/94-assembler.md
// §9.ar). Once `sd sN, off(sp)` has saved it, the body may write sN
// freely — the register allocator's `lw sN, k(sp)` to hold a working
// value — and only `ret` enforces the contract, by refusing a register
// written and not restored from its own slot. Reading any other frame
// load as a mis-matched restore refused 123 candidate forms whose
// prologue and epilogue agreed perfectly.
func TestRV64CalleeSavedMayBeUsedOnceSaved(t *testing.T) {
	decl := "pick: (value: u32) -> u32"
	check := func(body string) []string {
		unit, errs := ParseUnit("s.rv64.oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		sig, _ := parseSignature(decl)
		return Check(unit.Functions[0], sig, nil)
	}
	// Saved at 0(sp), used as a working register at 12(sp), restored from
	// its own slot before ret.
	used := "  bind a0 = value\n  clobber t0, t1, a0\n  frame 32\n  addi sp, sp, -32\n  sd s1, 0(sp)\n  sw a0, 12(sp)\n  lw s1, 12(sp)\n  addw t0, s1, a0\n  mv a0, t0\n  ld s1, 0(sp)\n  addi sp, sp, 32\n  ret"
	if findings := check(used); len(findings) != 0 {
		t.Fatalf("a saved register used and then restored must pass: %v", findings)
	}
	// An eight-byte load from another slot is a use as well, not a
	// restore from the wrong place.
	wide := "  bind a0 = value\n  clobber t0, t1, a0\n  frame 32\n  addi sp, sp, -32\n  sd s1, 0(sp)\n  sd a0, 16(sp)\n  ld s1, 16(sp)\n  mv a0, s1\n  ld s1, 0(sp)\n  addi sp, sp, 32\n  ret"
	if findings := check(wide); len(findings) != 0 {
		t.Fatalf("an eight-byte load from another slot is a use: %v", findings)
	}
	cases := []struct{ name, body, want string }{
		{"used and never restored",
			"  bind a0 = value\n  clobber t0, a0\n  frame 32\n  addi sp, sp, -32\n  sd s1, 0(sp)\n  sw a0, 12(sp)\n  lw s1, 12(sp)\n  mv a0, s1\n  addi sp, sp, 32\n  ret",
			"written but not restored"},
		{"restored then written again",
			"  bind a0 = value\n  clobber t0, a0\n  frame 32\n  addi sp, sp, -32\n  sd s1, 0(sp)\n  ld s1, 0(sp)\n  sw a0, 12(sp)\n  lw s1, 12(sp)\n  mv a0, s1\n  addi sp, sp, 32\n  ret",
			"written but not restored"},
		{"written before it is saved",
			"  bind a0 = value\n  clobber t0, a0\n  frame 32\n  addi sp, sp, -32\n  sw a0, 12(sp)\n  lw s1, 12(sp)\n  mv a0, s1\n  addi sp, sp, 32\n  ret",
			"callee-saved"},
	}
	for _, tc := range cases {
		findings := check(tc.body)
		if len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), tc.want) {
			t.Fatalf("%s: want %q, got %v", tc.name, tc.want, findings)
		}
	}
}
