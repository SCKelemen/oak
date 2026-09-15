package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Check elision on the RV64 lane (docs/spec/94-assembler.md §9.ae): the
// loop's `i < len(b)` test compares the zero-extended index with the
// normalized length, the proven element read reuses that register with no
// guard of its own, the seam checker admits it from the test's fact, and
// the verifier still proves the body by loop coupling.
const nativeRV64ElisionProgram = `
byte_total: (b: []u8) -> u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(b) {
    acc = acc + u32(b[i])
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  buf: [4]u8 = [u8(1), u8(2), u8(3), u8(4)]
  i32_bits_u32(byte_total(view(&buf))) + 32
}
`

func TestE2ENativeRV64Elision(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("elision.oak", nativeRV64ElisionProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "byte_total: 1 element guard(s) elided") {
		t.Fatalf("the proven read must be elided on the RV64 lane:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit byte_total: proven equal") || !strings.Contains(joined, "coupled inductively") {
		t.Fatalf("byte_total must stay proven by loop coupling with the guard elided:\n%s", joined)
	}
	for _, f := range model.AsmFunctions {
		if f.Name != "byte_total" {
			continue
		}
		traps, zext := 0, false
		for i := 1; i < len(f.Items); i++ {
			instr, isInstr := f.Items[i].(asm.Instruction)
			if !isInstr {
				continue
			}
			if instr.Mnemonic == "bgeu" {
				if sym, isSym := instr.Operands[len(instr.Operands)-1].(asm.Symbol); isSym && strings.HasPrefix(sym.Name, "trap") {
					traps++
				}
			}
			if prev, ok := f.Items[i-1].(asm.Instruction); ok && prev.Mnemonic == "slli" && instr.Mnemonic == "srli" {
				zext = true
			}
		}
		if traps != 0 {
			t.Errorf("the loop body must carry no element guard, found %d bgeu to the trap", traps)
		}
		if !zext {
			t.Errorf("the exit test must zero-extend the index (slli 32; srli 32) before comparing it with the normalized length")
		}
	}
}
