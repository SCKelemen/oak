package asm

import (
	"strings"
	"testing"
)

// The RV64 checker's rule for package globals (docs/spec/94-assembler.md
// §9): `la rd, G` of a declared global is a writable cell of the global's
// width, accessed whole at offset 0; an offset, another width, or an
// undeclared symbol is refused.
func TestRV64CheckerGlobals(t *testing.T) {
	decl := "bump: (k: u32) -> u32"
	globals := map[string]Global{"st": {Type: "u32", Bits: 32}}
	check := func(body string) []string {
		unit, errs := ParseUnit("g.rv64.oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) != 0 {
			t.Fatal(errs)
		}
		unit.Functions[0].Globals = globals
		sig, _ := parseSignature(decl)
		return Check(unit.Functions[0], sig, nil)
	}
	if findings := check("  bind a0 = k\n  clobber t0, t1\n  la t0, st\n  lw t1, 0(t0)\n  addw t1, t1, a0\n  sw t1, 0(t0)\n  mv a0, t1\n  ret"); len(findings) != 0 {
		t.Fatalf("a load and store of a global at its width must pass: %v", findings)
	}
	cases := []struct{ name, body, want string }{
		{"offset", "  bind a0 = k\n  clobber t0\n  la t0, st\n  lw a0, 4(t0)\n  ret", "one cell of 4 bytes"},
		{"wider", "  bind a0 = k\n  clobber t0\n  la t0, st\n  ld a0, 0(t0)\n  ret", "one cell of 4 bytes"},
		{"narrower", "  bind a0 = k\n  clobber t0\n  la t0, st\n  lbu a0, 0(t0)\n  ret", "one cell of 4 bytes"},
		{"unknown symbol", "  bind a0 = k\n  clobber t0\n  la t0, other\n  lw a0, 0(t0)\n  ret", "not a constant data symbol or global"},
	}
	for _, tc := range cases {
		findings := check(tc.body)
		if len(findings) == 0 {
			t.Errorf("%s: must be refused", tc.name)
			continue
		}
		if !strings.Contains(strings.Join(findings, "\n"), tc.want) {
			t.Errorf("%s: want %q, got %v", tc.name, tc.want, findings)
		}
	}
}
