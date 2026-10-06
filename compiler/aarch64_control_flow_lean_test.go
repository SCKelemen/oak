package compiler

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
	"github.com/SCKelemen/oak/target"
)

const aarch64ControlFlowProgram = `
walk32: (n: u32, stop: Bool): u32 {
  i: u32 = 0
  acc: u32 = 0
  while i < n && !stop {
    acc = acc + i
    i = i + u32(1)
  }
  acc
}

walk64: (n: u64, stop: Bool): u64 {
  i: u64 = 0
  acc: u64 = 0
  while i < n && !stop {
    acc = acc + i
    i = i + u64(1)
  }
  acc
}
`

// Actual source -> selected assembly -> machine CFG -> ELF words. Each local
// branch generates a Lean theorem valid for every register/flag state at that
// PC. These finite source witnesses do not prove the whole Go compiler.
func TestAArch64ControlFlowSourceObjectLean(t *testing.T) {
	comp := New().WithSource("control_flow.oak", aarch64ControlFlowProgram).
		WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchArm64}).
		WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	object, err := comp.EmitNativeObject(asm.ELF).Get()
	if err != nil {
		t.Fatal(err)
	}
	var examples []string
	forward, backward, conditional, functions := 0, 0, 0, 0
	conditionBits := map[string]int{"eq": 0, "ne": 1, "cs": 2, "hs": 2, "cc": 3, "lo": 3, "mi": 4, "pl": 5,
		"vs": 6, "vc": 7, "hi": 8, "ls": 9, "ge": 10, "lt": 11, "gt": 12, "le": 13, "al": 14, "nv": 15}
	for _, fn := range model.AsmFunctions {
		if fn.Name != "walk32" && fn.Name != "walk64" {
			continue
		}
		functions++
		if verdict := model.NativeVerdicts[fn.Name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s was not translation-validated: %s (%s)", fn.Name, verdict.Kind, verdict.Message)
		}
		words := aarch64ObjectFunctionWords(t, object, "oak_"+fn.Name)
		labels := map[string]int{}
		var instructions []asm.Instruction
		for _, item := range fn.Items {
			switch it := item.(type) {
			case asm.Label:
				labels[it.Name] = 4 * len(instructions)
			case asm.Instruction:
				if it.Mnemonic == "adrl" {
					t.Fatal("fixture acquired a multiword pseudo; extend its layout witness")
				}
				instructions = append(instructions, it)
			default:
				t.Fatalf("fixture acquired padding/unknown item %T; extend its layout witness", item)
			}
		}
		if len(words) != len(instructions) {
			t.Fatalf("%s: %d object words versus %d emitted instructions", fn.Name, len(words), len(instructions))
		}
		lifted, err := machine.Lift(fn)
		if err != nil {
			t.Fatal(err)
		}
		for _, block := range lifted.Blocks {
			if len(block.Instrs) == 0 {
				continue
			}
			last := block.Instrs[len(block.Instrs)-1]
			if !last.Branch {
				continue
			}
			instr := last.Asm
			name := instr.Operands[len(instr.Operands)-1].(asm.Symbol).Name
			to, exists := labels[name]
			if !exists || len(block.Succs) == 0 || block.Succs[0].Label != name {
				t.Fatalf("%s: branch target %s does not agree with the machine CFG", fn.Name, name)
			}
			pc := last.Index * 4
			if to < pc {
				backward++
			} else {
				forward++
			}
			word := words[last.Index]
			state := fmt.Sprintf("⟨%d, flags, regs⟩", pc)
			if instr.Mnemonic == "b" && instr.Cond == "" {
				examples = append(examples, fmt.Sprintf("example (flags : Flags) (regs : Registers) : stepControl 0x%08x#32 %s = some ⟨true, ⟨%d, flags, regs⟩⟩ := jumpWord_step (by decide) flags regs", word, state, to))
				continue
			}
			kind, low := "bcond", 0
			switch instr.Mnemonic {
			case "b", "b.":
				var ok bool
				low, ok = conditionBits[instr.Cond]
				if !ok {
					t.Fatalf("unmodeled condition %s", instr.Cond)
				}
			case "cbz", "cbnz":
				reg := instr.Operands[0].(asm.Register)
				kind, low = instr.Mnemonic+"32", reg.Num
				if reg.Class == asm.ClassX {
					kind = instr.Mnemonic + "64"
				}
			default:
				t.Fatalf("fixture acquired unmodeled branch %s", instr.Mnemonic)
			}
			conditional++
			if len(block.Succs) != 2 || block.Succs[1].Index != block.Index+1 {
				t.Fatalf("%s: conditional fall-through disagrees with machine layout", fn.Name)
			}
			examples = append(examples, fmt.Sprintf("example (flags : Flags) (regs : Registers) : stepControl 0x%08x#32 %s = some (branchTo .%s %d %d %s) := localWord_step (by decide) flags regs", word, state, kind, low, to, state))
		}
	}
	if functions != 2 || forward == 0 || backward == 0 || conditional < 2 {
		t.Fatalf("missing source/CFG witnesses: functions=%d forward=%d backward=%d conditional=%d", functions, forward, backward, conditional)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_ARM64_COND19_LEAN") != "" {
			t.Fatal("lake required for ARM64 source/object branch correspondence")
		}
		t.Skip("lake not on PATH; ARM64 proof workflow requires this oracle")
	}
	root := filepath.Join("..", "spec", "lean")
	build := exec.Command(lake, "build", "Oak.AArch64ControlFlow")
	build.Dir = root
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build control-flow proof: %v\n%s", err, out)
	}
	path := filepath.Join(t.TempDir(), "SourceObject.lean")
	header := "import Oak.AArch64ControlFlow\nopen Oak.AArch64ControlFlow Oak.AArch64BranchExecution Oak.AssemblerSemantics\n"
	if err := os.WriteFile(path, []byte(header+strings.Join(examples, "\n")+"\n"), 0600); err != nil {
		t.Fatal(err)
	}
	run := exec.Command(lake, "env", "lean", path)
	run.Dir = root
	if out, err := run.CombinedOutput(); err != nil {
		t.Fatalf("source/object branch proofs: %v\n%s", err, out)
	}
	t.Logf("Lean checked %d source/object branches for all register/flag states", len(examples))
}
