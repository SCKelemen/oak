package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Check elision over a constant table (docs/spec/94-assembler.md §9 "Check
// elision", masked indices): a table of eight bytes indexed by `x & 7` is
// proven in range by the typechecker (masked_under_length), lowered without
// its constant guard, and admitted by the checker from the mask's bound
// (Oak.Assembler.masked_index_bound); the verifier still proves the body.
const nativeMaskedTableProgram = `
SYMBOLS: [8]u8 = [8]u8{u8(97), u8(98), u8(99), u8(100), u8(101), u8(102), u8(103), u8(104)}

symbol_of: (x: u32) -> u8 = SYMBOLS[x & u32(7)]

main: (): i32 {
  assert(symbol_of(u32(0)) == u8(97))
  assert(symbol_of(u32(9)) == u8(98))
  assert(symbol_of(u32(4294967295)) == u8(104))
  42
}
`

func TestE2ENativeMaskedTableElision(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("masked.oak", nativeMaskedTableProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "symbol_of: 1 element guard(s) elided") {
		t.Fatalf("the masked table read must be elided:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit symbol_of: proven equal") {
		t.Fatalf("symbol_of must stay proven with the guard elided:\n%s", joined)
	}
	for _, f := range model.AsmFunctions {
		if f.Name != "symbol_of" {
			continue
		}
		for _, item := range f.Items {
			if instr, isInstr := item.(asm.Instruction); isInstr && instr.Mnemonic == "cmp" {
				t.Errorf("symbol_of must carry no constant guard, found %v", instr)
			}
		}
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_masked_table", comp); abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}
