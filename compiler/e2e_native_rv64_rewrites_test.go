package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

// Layer A on the RV64 lane (docs/spec/94-assembler.md §9.ag): the
// strength reduction of constant arithmetic is a body rewrite shared by
// every lane, so the RV64 lowering of a division, a remainder, and a
// multiplication by a power of two carries shifts and a mask, no divide
// or multiply, and the body proves against the rewritten body.
const nativeRV64RewritesProgram = `
page_index: (n: u32, k: u32) -> u32 {
  half: u32 = n / u32(2)
  page: u32 = k * u32(512)
  half + page + n % u32(8)
}
// An element read as the operand: the site's theorem abstracts the read
// as a parameter of the element type, so the rewrite applies here too.
half_at: (v: []u32, i: u32) -> u32 = v[i] / u32(2)
main: (): i32 = 0
`

func TestE2ENativeRV64Rewrites(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("rewrites.oak", nativeRV64RewritesProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if !strings.Contains(joined, "page_index: layer A — strength reduction ×3 decided at the bit level") {
		t.Fatalf("the three power-of-two sites must rewrite on the RV64 lane:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit page_index: proven equal") {
		t.Fatalf("page_index must prove against the rewritten body:\n%s", joined)
	}
	if !strings.Contains(joined, "half_at: layer A — strength reduction ×1 decided at the bit level") {
		t.Fatalf("the element-read site must rewrite through its abstracted theorem:\n%s", joined)
	}
	for _, f := range model.AsmFunctions {
		if f.Name != "page_index" && f.Name != "half_at" {
			continue
		}
		shifts, divides := 0, 0
		for _, item := range f.Items {
			instr, isInstr := item.(asm.Instruction)
			if !isInstr {
				continue
			}
			switch {
			case strings.HasPrefix(instr.Mnemonic, "srli") || strings.HasPrefix(instr.Mnemonic, "slli") || strings.HasPrefix(instr.Mnemonic, "and"):
				shifts++
			case strings.HasPrefix(instr.Mnemonic, "div") || strings.HasPrefix(instr.Mnemonic, "rem") || strings.HasPrefix(instr.Mnemonic, "mul"):
				divides++
			}
		}
		if (f.Name == "page_index" && shifts < 3) || shifts == 0 || divides != 0 {
			t.Fatalf("%s on RV64: want shifts and a mask, no divide or multiply; shifts %d, divides %d", f.Name, shifts, divides)
		}
	}
}
