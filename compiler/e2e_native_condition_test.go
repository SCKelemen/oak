package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
)

// Condition selection on the AArch64 lane (docs/spec/94-assembler.md §9
// "Condition selection"): a negation inverts the branch instead of
// materializing a Bool, a Bool variable in a register is tested where it
// lives, a small constant is the compare's immediate in a comparison and
// in a match arm, and a bitwise operation with an in-range constant is not
// masked again. The shapes are asserted on the lowered instructions and
// the values against the C backend.
const nativeConditionProgram = `
Op: type = Add | Sub | Mul

classify: (code: []u8): u32 {
  acc: u32 = 0
  i: u32 = 0
  seen_end: Bool = false
  while i < len(code) && !seen_end {
    b: u8 = code[i]
    op: u8 = b & u8(7)
    arg: u32 = u32(b >> u8(3))
    op ?
    | 0 => { acc = acc + arg }
    | 1 => { acc = acc * u32(3) }
    | 2 => { acc = acc ^ arg }
    | 7 => { seen_end = true }
    | _ => { acc = acc - arg }
    arg == u32(31) ? { acc = acc + u32(100) } | { }
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  code: [6]u8 = [u8(8), u8(17), u8(26), u8(251), u8(7), u8(255)]
  // 1, then 3, then 3 ^ 3 = 0, then 0 - 31 wrapping and + 100 (arg 31) = 69,
  // then the end marker; the last byte is never read.
  i32_bits_u32(classify(view(&code))) + 20
}
`

func TestE2ENativeConditionSelection(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("cond.oak", nativeConditionProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	var fn *asm.Function
	for _, f := range model.AsmFunctions {
		if f.Name == "classify" {
			fn = f
		}
	}
	if fn == nil {
		t.Fatalf("classify was not lowered natively:\n%s", strings.Join(infos, "\n"))
	}
	counts := map[string]int{}
	cmpImmediates, materializedCompares := 0, 0
	var previous asm.Instruction
	for _, item := range fn.Items {
		instr, isInstr := item.(asm.Instruction)
		if !isInstr {
			continue
		}
		counts[instr.Mnemonic]++
		if instr.Mnemonic == "cmp" && len(instr.Operands) == 2 {
			if _, isImm := instr.Operands[1].(asm.Immediate); isImm {
				cmpImmediates++
			} else if previous.Mnemonic == "movz" && len(previous.Operands) > 0 && previous.Operands[0] == instr.Operands[1] {
				materializedCompares++
			}
		}
		previous = instr
	}
	if counts["eor"] != 1 {
		// The one eor is `acc ^ arg`; `!seen_end` must not materialize one.
		t.Errorf("want exactly one eor (the xor of the body), got %d", counts["eor"])
	}
	if counts["cbnz"] < 1 && counts["ccmp"] < 1 {
		// Or, the exit tests fused (machine.FuseExits), the Bool's register
		// is the ccmp's operand against zero — still no materialized
		// compare.
		t.Errorf("`!seen_end` must branch on the Bool's own register with cbnz, or test it in a ccmp; mnemonics: %v", counts)
	}
	if materializedCompares != 0 {
		// The remaining movz are the multiplier 3 and the Bool `true`.
		t.Errorf("no literal should be materialized for a compare: %d; mnemonics: %v", materializedCompares, counts)
	}
	if counts["and"] != 1 || counts["lsr"] != 1 {
		// `b & u8(7)` is one and; `b >> u8(3)` is one lsr with no mask after
		// either (an unsigned value shifted right, or masked inside its
		// width, stays normalized).
		t.Errorf("want one and and one lsr with no normalizing mask, got %d and %d; mnemonics: %v", counts["and"], counts["lsr"], counts)
	}
	if cmpImmediates < 5 {
		// Four literal arms and `arg == u32(31)`.
		t.Errorf("want the match arms and the equality to compare against immediates, got %d", cmpImmediates)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_condition", comp)
	if abnormal || code != 89 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 89\n%s", code, abnormal, strings.Join(infos, "\n"))
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_condition_c", New().WithSource("cond.oak", nativeConditionProgram)); abnormal || code != 89 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 89", code, abnormal)
	}
}
