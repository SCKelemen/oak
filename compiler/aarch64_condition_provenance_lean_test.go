package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

func TestAArch64ConditionProvenanceSourceObjectLean(t *testing.T) {
	operations := []struct{ symbol, name string }{{"==", "eq"}, {"!=", "ne"}, {"<", "lt"}, {"<=", "le"}, {">", "gt"}, {">=", "ge"}}
	type specification struct{ width, predicate string }
	want := map[string]specification{}
	var source strings.Builder
	for _, typ := range []string{"u32", "i32", "u64", "i64"} {
		for _, op := range operations {
			name := "compare_" + typ + "_" + op.name
			fmt.Fprintf(&source, "%s: (a: %s, b: %s): Bool = a %s b\n", name, typ, typ, op.symbol)
			width, predicate := "w32", op.name
			if strings.HasSuffix(typ, "64") {
				width = "x64"
			}
			if predicate != "eq" && predicate != "ne" {
				prefix := "u"
				if typ[0] == 'i' {
					prefix = "s"
				}
				predicate = prefix + predicate
			}
			want[name] = specification{width, predicate}
		}
	}
	comp := New().WithSource("comparisons.oak", source.String()).
		WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}).WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	object, err := comp.EmitNativeObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	var examples []string
	for _, fn := range model.AsmFunctions {
		spec, ok := want[fn.Name]
		if !ok {
			continue
		}
		if verdict := model.NativeVerdicts[fn.Name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s lacks translation validation: %s (%s)", fn.Name, verdict.Kind, verdict.Message)
		}
		words := aarch64ObjectFunctionWords(t, object, "oak_"+fn.Name)
		var instructions []asm.Instruction
		for _, item := range fn.Items {
			switch it := item.(type) {
			case asm.Label:
			case asm.Instruction:
				if it.Mnemonic == "adrl" {
					t.Fatal("comparison fixture acquired multiword pseudo")
				}
				instructions = append(instructions, it)
			default:
				t.Fatalf("comparison fixture acquired padding/unknown item %T", item)
			}
		}
		if len(words) != len(instructions) {
			t.Fatalf("%s instruction/object lengths disagree", fn.Name)
		}
		found := 0
		for i := 0; i+1 < len(instructions); i++ {
			cmp, set := instructions[i], instructions[i+1]
			if cmp.Mnemonic != "cmp" || set.Mnemonic != "cset" {
				continue
			}
			rn, okN := cmp.Operands[0].(asm.Register)
			rm, okM := cmp.Operands[1].(asm.Register)
			rd, okD := set.Operands[0].(asm.Register)
			if !okN || !okM || !okD || rd.Class != asm.ClassW {
				t.Fatalf("%s comparison is outside register CMP/CSET W", fn.Name)
			}
			// The fixture proves the raw input-register comparison, without
			// assuming that earlier moves computed the operand values.
			if i != 0 || rn.Num != 0 || rm.Num != 1 {
				t.Fatalf("%s acquired an input prefix/reordering; extend the provenance witness", fn.Name)
			}
			proof := fmt.Sprintf("(show checkProducer .%s .%s %d %d %d 0x%08x#32 0x%08x#32 = true from by decide)", spec.width, spec.predicate, rn.Num, rm.Num, rd.Num, words[i], words[i+1])
			examples = append(examples, fmt.Sprintf("example (s : State) : prepare 0x%08x#32 0x%08x#32 s = some (produced .%s .%s %d %d %d s) ∧ boolValue (produced .%s .%s %d %d %d s).regs %d = sourceValue .%s .%s %d %d s := checked_prepare _ _ _ _ _ _ _ %s s", words[i], words[i+1], spec.width, spec.predicate, rn.Num, rm.Num, rd.Num, spec.width, spec.predicate, rn.Num, rm.Num, rd.Num, rd.Num, spec.width, spec.predicate, rn.Num, rm.Num, proof))
			found++
		}
		if found != 1 {
			t.Fatalf("%s has %d CMP/CSET pairs, want one: %v", fn.Name, found, instructions)
		}
	}
	if len(examples) != len(want) {
		t.Fatalf("checked %d source comparisons, want %d", len(examples), len(want))
	}
	checkAArch64SourceLean(t, "AArch64ConditionProvenance", examples)
}
