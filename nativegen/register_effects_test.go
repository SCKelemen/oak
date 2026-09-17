package nativegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func registerEffectItems(t *testing.T, body string) []asm.Item {
	t.Helper()
	unit, errs := asm.ParseUnit("effects.oakasm", "f: (a: u32, b: u32) -> u32 = {\n bind w0 = a\n bind w1 = b\n clobber x9, x10, x11, x19, x20, v9, v10\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	return unit.Functions[0].Items
}

func TestPairedLoadGeneralEffects(t *testing.T) {
	mask := func(regs []int) uint32 {
		var result uint32
		for _, r := range regs {
			result |= 1 << uint(r)
		}
		return result
	}
	for _, test := range []struct {
		body          string
		reads, writes []int
	}{
		{"ldp x9, x10, [x0]", []int{0}, []int{9, 10}},
		{"ldp w9, w10, [x0]", []int{0}, []int{9, 10}},
		{"ldpsw x9, x10, [x0]", []int{0}, []int{9, 10}},
		{"ldp x9, x10, [x10]", []int{10}, []int{9, 10}},
		{"ldp x9, x10, [x0], #16", []int{0}, []int{0, 9, 10}},
		{"ldp x9, x10, [x0, #16]!", []int{0}, []int{0, 9, 10}},
		{"ldp q9, q10, [x0]", []int{0}, nil},
		{"ldp q9, q10, [x0], #32", []int{0}, []int{0}},
		{"stp x9, x10, [x0]", []int{0, 9, 10}, nil},
		{"stp x9, x10, [x0], #16", []int{0, 9, 10}, []int{0}},
		{"stp q9, q10, [x0]", []int{0}, nil},
		{"str q10, [x0]", []int{0}, nil},
		{"ldp xzr, x10, [x0]", []int{0}, []int{10}},
		{"stp xzr, x10, [x0]", []int{0, 10}, nil},
	} {
		t.Run(test.body, func(t *testing.T) {
			ins := registerEffectItems(t, test.body)[0].(asm.Instruction)
			var reads uint32
			for r := 0; r <= 30; r++ {
				if readsGeneral(ins, r) {
					reads |= 1 << uint(r)
				}
			}
			if reads != mask(test.reads) || mask(writtenGeneral(ins)) != mask(test.writes) {
				t.Fatalf("reads=%x writes=%x, want reads=%x writes=%x", reads, mask(writtenGeneral(ins)), mask(test.reads), mask(test.writes))
			}
		})
	}
}

func TestPairLoadRenamingPreservesBothDestinations(t *testing.T) {
	for _, mnemonic := range []string{"ldp", "ldpsw"} {
		original := registerEffectItems(t, mnemonic+" x9, x10, [x10]")[0].(asm.Instruction)
		renamed := renameReads(original, 10, xr(4))
		if got := Describe(&asm.Function{Items: []asm.Item{renamed}}); !strings.Contains(got, mnemonic+" x9, x10, [x4]") {
			t.Fatalf("only the input address may be renamed:\n%s", got)
		}
		if original.Operands[2].(asm.Memory).Base.Num != 10 {
			t.Fatal("renaming mutated the original instruction")
		}
		named := registersNamed([]asm.Item{original})
		if !named[9] || !named[10] {
			t.Fatal("both output registers must remain reserved")
		}
		independent := registerEffectItems(t, mnemonic+" x9, x10, [x19]")[0].(asm.Instruction)
		if !registersNamed([]asm.Item{independent})[10] {
			t.Fatal("an output-only second destination must remain reserved")
		}
	}
	vectorStore := registerEffectItems(t, "str q10, [x10]")[0].(asm.Instruction)
	if !readsOnlyAsClass(vectorStore, 10, asm.ClassX) {
		t.Fatal("the vector data operand is not a differently-sized GPR read")
	}
	renamed := renameReads(vectorStore, 10, xr(4))
	if !strings.Contains(Describe(&asm.Function{Items: []asm.Item{renamed}}), "str q10, [x4]") {
		t.Fatal("a same-numbered vector data register must not be renamed with the base")
	}
}

func TestCleanupPairLoadOperands(t *testing.T) {
	out, _ := cleanupText(t, "mov x10, x4\nldp x9, x10, [x0]\nstr x10, [x19]\nret")
	if !strings.Contains(out, "ldp x9, x10, [x0]") || strings.Contains(out, "ldp x9, x4") {
		t.Fatalf("a destination-only operand is not a copy consumer:\n%s", out)
	}
	out, _ = cleanupText(t, "mov x10, x4\nldp x9, x10, [x10]\nstr x10, [x19]\nret")
	if !strings.Contains(out, "ldp x9, x10, [x4]") || strings.Contains(out, "mov x10, x4") {
		t.Fatalf("forward the base input but retain the loaded output:\n%s", out)
	}
	for _, access := range []string{"ldp x9, x11, [x10], #16", "ldp x9, x11, [x10, #16]!", "ldr x9, [x10], #8", "stp x9, x11, [x10], #16"} {
		out, _ := cleanupText(t, "mov x10, x4\n"+access+"\nstr x10, [x19]\nret")
		if !strings.Contains(out, "mov x10, x4") || !strings.Contains(out, access) {
			t.Fatalf("writeback may not migrate to the source register:\n%s", out)
		}
	}
}

func TestPairedLoadKillsEarlierDestinationValue(t *testing.T) {
	items := registerEffectItems(t, "mov x10, x4\nldp x9, x10, [x0]\nstr x10, [x19]\nret")
	if liveAfter(items)[0]&(1<<10) != 0 {
		t.Fatal("the second loaded output does not read the earlier x10 value")
	}
	items = registerEffectItems(t, "mov x10, x4\nldp x9, x10, [x10]\nstr x10, [x19]\nret")
	if liveAfter(items)[0]&(1<<10) == 0 {
		t.Fatal("an aliased memory base still reads the earlier x10 value")
	}
}

func TestLivenessKeepsConditionalFallthrough(t *testing.T) {
	for _, mnemonic := range []string{"b", "b."} {
		items := registerEffectItems(t, "cmp w0, w1\nb.eq done\nstr x10, [x19]\ndone:\nret")
		branch := items[1].(asm.Instruction)
		branch.Mnemonic = mnemonic
		items[1] = branch
		if liveAfter(items)[1]&(1<<10) == 0 {
			t.Fatalf("%s with condition %q lost its fallthrough read", mnemonic, branch.Cond)
		}
	}
}

func TestLICMKeepsWritebackBaseCopy(t *testing.T) {
	items := registerEffectItems(t, "loop_1:\ncmp w2, w1\nb.hs done_2\nmov x10, x0\nldp x9, x11, [x10], #16\nstr x10, [x19]\nadd w2, w2, #1\nb loop_1\ndone_2:\nret")
	out, _, _, _ := hoistInvariants(items, registersNamed(items), map[string]map[int]bool{}, nil, nil, "trap_3")
	text := Describe(&asm.Function{Items: out})
	if !strings.Contains(text, "mov x10, x0") || !strings.Contains(text, "ldp x9, x11, [x10], #16") {
		t.Fatalf("LICM may not turn a read/write base into an ordinary renamed input:\n%s", text)
	}
}
