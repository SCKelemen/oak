package compiler

// A shift by a named module constant lowers as a shift by a literal does
// (docs/spec/90-backend.md §16): one immediate shift, no register for the
// count and no range check before it. The page walkers extract their
// indices as `(ipa >> l0_shift) & l0_mask` over declared constants; before
// the fold each such shift cost a `movz`, a `cmp` against the width, a
// trap branch, and a register shift. A named count at or beyond the width
// keeps the run-time check, which traps as the semantics say
// (10-syntax.md §3b).

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/target"
)

const nativeConstantShiftProgram = `l0_shift: u64 = u64(25)
l0_mask: u64 = u64(127)
lane: u32 = u32(7)
too_far: u64 = u64(64)

index0: (ipa: u64): u64 { (ipa >> l0_shift) & l0_mask }
scaled: (x: u32): u32 { x << lane }
over: (x: u64): u64 { x >> too_far }

main: (): i32 {
  a: u64 = index0(u64(3) << u64(25))
  b: u32 = scaled(u32(3))
  (a == u64(3) && b == u32(384)) ? 42 | 1
}
`

// shiftShape counts the immediate shifts, register shifts, and width
// compares in a unit.
func shiftShape(fn *asm.Function, immediate, register, compare func(asm.Instruction) bool) (imm, reg, cmp int) {
	for _, item := range fn.Items {
		ins, isIns := item.(asm.Instruction)
		if !isIns {
			continue
		}
		switch {
		case immediate(ins):
			imm++
		case register(ins):
			reg++
		case compare(ins):
			cmp++
		}
	}
	return
}

func TestE2ENativeConstantShiftCounts(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("cshift.oak", nativeConstantShiftProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	isShift := func(ins asm.Instruction) bool { return ins.Mnemonic == "lsr" || ins.Mnemonic == "lsl" }
	lastImmediate := func(ins asm.Instruction) (asm.Immediate, bool) {
		if len(ins.Operands) == 0 {
			return asm.Immediate{}, false
		}
		imm, isImm := ins.Operands[len(ins.Operands)-1].(asm.Immediate)
		return imm, isImm
	}
	immediate := func(ins asm.Instruction) bool {
		_, isImm := lastImmediate(ins)
		return isShift(ins) && isImm
	}
	register := func(ins asm.Instruction) bool { return isShift(ins) && !immediate(ins) }
	compare := func(ins asm.Instruction) bool {
		imm, isImm := lastImmediate(ins)
		return ins.Mnemonic == "cmp" && isImm && (imm.Value == 32 || imm.Value == 64)
	}
	for _, name := range []string{"index0", "scaled"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		imm, reg, cmp := shiftShape(units[name], immediate, register, compare)
		if imm != 1 || reg != 0 || cmp != 0 {
			t.Fatalf("%s: a named constant count is one immediate shift, no register shift and no width check; got %d immediate, %d register, %d compares", name, imm, reg, cmp)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must stay proven:\n%s", name, joined)
		}
	}
	if imm, reg, cmp := shiftShape(units["over"], immediate, register, compare); imm != 0 || reg != 1 || cmp != 1 {
		t.Fatalf("over: a named count at the width keeps the register shift behind its check; got %d immediate, %d register, %d compares", imm, reg, cmp)
	}
	_, code, abnormal := buildAndRunFrom(t, "cshift", comp)
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
}

func TestE2ENativeRV64ConstantShiftCounts(t *testing.T) {
	var infos []string
	tgt := target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}
	comp := New().WithSource("cshift.oak", nativeConstantShiftProgram).WithTarget(tgt).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v\n%s", err, strings.Join(infos, "\n"))
	}
	units := map[string]*asm.Function{}
	for _, fn := range model.AsmFunctions {
		units[fn.Name] = fn
	}
	joined := strings.Join(infos, "\n")
	immediate := func(ins asm.Instruction) bool {
		return ins.Mnemonic == "srli" || ins.Mnemonic == "slli" || ins.Mnemonic == "srliw" || ins.Mnemonic == "slliw"
	}
	register := func(ins asm.Instruction) bool {
		return ins.Mnemonic == "srl" || ins.Mnemonic == "sll" || ins.Mnemonic == "srlw" || ins.Mnemonic == "sllw"
	}
	compare := func(ins asm.Instruction) bool { return ins.Mnemonic == "bgeu" }
	for _, name := range []string{"index0", "scaled"} {
		if units[name] == nil {
			t.Fatalf("%s was not lowered natively:\n%s", name, joined)
		}
		if imm, reg, cmp := shiftShape(units[name], immediate, register, compare); imm != 1 || reg != 0 || cmp != 0 {
			t.Fatalf("%s: one immediate shift and no width check; got %d immediate, %d register, %d compares", name, imm, reg, cmp)
		}
		if !strings.Contains(joined, "asm unit "+name+": proven") {
			t.Fatalf("%s must stay proven:\n%s", name, joined)
		}
	}
	if imm, reg, cmp := shiftShape(units["over"], immediate, register, compare); imm != 0 || reg != 1 || cmp != 1 {
		t.Fatalf("over: a named count at the width keeps the register shift behind its check; got %d immediate, %d register, %d compares", imm, reg, cmp)
	}
}
