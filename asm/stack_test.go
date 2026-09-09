package asm

import (
	"strings"
	"testing"
)

// The operand-stack shorthand desugars into bound-register instructions the
// seam checker accepts, and refuses malformed stacks.
func TestOperandStackShorthand(t *testing.T) {
	decl := "add_asm: (left, right: u32) -> u32"
	unit, errs := ParseUnit("stack.oakasm", decl+" = {\n  push left\n  push right\n  add\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	if len(fn.Bindings) != 2 || fn.Bindings[0].Register.Text != "w0" || fn.Bindings[1].Register.Text != "w1" {
		t.Fatalf("shorthand must bind both parameters at their contract registers, got %+v", fn.Bindings)
	}
	sig, _ := parseSignature(decl)
	if findings := Check(fn, sig, nil); len(findings) != 0 {
		t.Fatalf("desugared body must pass the checker: %v", findings)
	}
	var mnemonics []string
	for _, item := range fn.Items {
		if instr, ok := item.(Instruction); ok {
			mnemonics = append(mnemonics, instr.Mnemonic)
		}
	}
	if strings.Join(mnemonics, " ") != "add mov ret" {
		t.Fatalf("unexpected desugaring: %v", mnemonics)
	}

	// Immediates, chained operations, and a 64-bit result.
	decl64 := "scale: (a: u64) -> u64"
	unit, errs = ParseUnit("stack64.oakasm", decl64+" = {\n  push a\n  push #2\n  add\n  push #3\n  lsl\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig64, _ := parseSignature(decl64)
	if findings := Check(unit.Functions[0], sig64, nil); len(findings) != 0 {
		t.Fatalf("chained shorthand must pass the checker: %v", findings)
	}

	for name, body := range map[string]string{
		"underflow":      "  push left\n  add",
		"leftover":       "  push left\n  push right\n  push #1\n  add",
		"not a param":    "  push nothing\n  push right\n  add",
		"mixed explicit": "  push left\n  add w0, w0, w1",
		"explicit binds": "  bind w0 = left\n  push left\n  push right\n  add",
	} {
		_, errs := ParseUnit(name+".oakasm", decl+" = {\n"+body+"\n}\n")
		if len(errs) == 0 {
			t.Fatalf("%s: malformed shorthand must be refused", name)
		}
	}
}
