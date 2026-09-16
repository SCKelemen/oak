package machine

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
)

// FPR is the RV64 floating-point file f0–f31 (the F and D extensions).
// AArch64 keeps its floats in the vector file (VEC).
const FPR Class = 3

// target is what the lift, the webs, the allocator, and the promotion
// know of one lane: the instruction shapes, the register files and their
// spellings, the procedure-call contract, and the lowering's prologue and
// epilogue.
type target struct {
	arch string
	// shapes are the instructions the lift knows on this lane.
	shapes map[string]shape
	// regOf maps an assembly register to a Reg with its view's width; ok
	// is false for sp and the zero register.
	regOf func(asm.Register) (reg Reg, bits int, lane bool, ok bool, err error)
	// spell rewrites a register operand to a physical register, keeping
	// its view.
	spell func(asm.Register, Reg) asm.Register
	// reserved registers are never renamed.
	reserved func(Reg) bool
	// calleeSaved registers survive a call.
	calleeSaved func(Reg) bool
	// callUses, callDefs, and retUses are the contract registers a call
	// reads and may write, and a return reads.
	callUses, callDefs, retUses []Access
	// kind classes an instruction: a call, a return, a trap, a branch
	// (conditional or not), or one the lift refuses.
	kind func(asm.Instruction) (call, ret, trap, branch bool, err error)
	// conditional reports a branch that may fall through.
	conditional func(asm.Instruction) bool
	// copyOf recognizes a register-to-register copy and its width.
	copyOf func(asm.Instruction) (bits int, ok bool)
	// callerSaved lists the caller-saved registers allocation may take for
	// ranges that cross no call, beyond those the body wrote.
	callerSaved []Reg
	// slotAccess reads a plain frame-slot load or store: the register
	// operand's index, the width, whether it stores.
	slotAccess func(asm.Instruction) (op int, bits int, store bool, ok bool)
	// promotable reports a slot width and class promotion handles.
	promotable func(class Class, bits int) bool
	// slotCandidates orders the registers a slot of a class may take.
	slotCandidates func(class Class) []Reg
	// slotCopy spells the copy that replaces a slot access.
	slotCopy func(r Reg, reg asm.Register, s slot, store bool, line int) asm.Instruction
	// clobber spells a register for the clobber list.
	clobber func(Reg) asm.Register
	// pure reports an instruction with no effect beyond its register
	// results: no store, call, branch, compare or flag write, atomic, or
	// system effect, and no load from anywhere but the frame. Such an
	// instruction may go when no one reads its results.
	pure func(asm.Instruction) bool
	// readsFlags reports an instruction whose result depends on the
	// condition flags (csel, cset, ...): pure, but not movable past the
	// compare that sets them.
	readsFlags func(asm.Instruction) bool
	// frame is the lowering's prologue and epilogue shape (growCalleeSaved).
	frame frameShape
	// barrier reports an instruction the scheduler never moves or moves
	// past: a call, a return, a trap, a branch, a memory barrier, an
	// atomic, an sp write, a system instruction.
	barrier func(*Instr) bool
	// latency is the cycles an instruction's result takes on the lane's
	// reference core (the scheduler's and the stall estimate's model).
	latency func(asm.Instruction) int
	// writesFlags reports an instruction that sets the condition flags.
	writesFlags func(asm.Instruction) bool
	// increment reads `r = r + k` / `r = r - k` with an immediate: the
	// register and its signed step (recurrence analysis).
	increment func(asm.Instruction) (reg Reg, step int64, ok bool)
	// constant reads an instruction that materializes a constant into a
	// register (mov/movz #k; li/mv from zero).
	constant func(asm.Instruction) (int64, bool)
	// exitTest reads a loop's compare: the registers compared (in operand
	// order, matching the instruction's Uses), and an immediate when the
	// second operand is one.
	exitTest func(asm.Instruction) (regs []Reg, imm int64, hasImm bool, ok bool)
}

// frameShape describes the lowering's frame code on a lane: the store
// that saves the return address (with the frame pointer on AArch64), the
// load that restores it, the callee-saved registers in the order the
// lowering saves them, and how a save and a restore are spelled.
type frameShape struct {
	// isPairSave / isPairRestore recognize the frame pair's save and
	// restore (`stp x29, x30, [sp, #o]` / `ldp`; `sd ra, o(sp)` / `ld`).
	isPairSave, isPairRestore func(asm.Instruction) (offset int64, ok bool)
	// saveOrder lists the callee-saved general registers in the order the
	// lowering saves them.
	saveOrder []Reg
	// isSave recognizes a save of callee-saved registers to the frame: the
	// registers stored and the offset.
	isSave func(asm.Instruction) (regs []Reg, offset int64, ok bool)
	// save and restore spell one register's save and restore.
	save, restore func(r Reg, offset int64, line int) asm.Instruction
	// pairArea is how many bytes the frame pair's save occupies before the
	// callee-saved area.
	pairArea int64
}

// targetFor picks the lane's target.
func targetFor(arch string) (*target, error) {
	switch arch {
	case "", asm.ArchArm64:
		return arm64Target, nil
	case asm.ArchRV64:
		return rv64Target, nil
	}
	return nil, fmt.Errorf("machine: the %s lane is not lifted", arch)
}

// ---- AArch64 -----------------------------------------------------------

var arm64Target = &target{
	arch:   asm.ArchArm64,
	shapes: shapes,
	regOf:  regOf,
	spell:  spell,
	reserved: func(r Reg) bool {
		return r.Class == GPR && (r.Num == 8 || r.Num == 18 || r.Num == 29 || r.Num == 30)
	},
	calleeSaved: func(r Reg) bool {
		if r.Class == GPR {
			return r.Num >= 19 && r.Num <= 28
		}
		return r.Class == VEC && r.Num >= 8 && r.Num <= 15
	},
	callUses: append(gprs(0, 8, 64), vecs(0, 7, 128)...),
	callDefs: append(append(gprs(0, 18, 64), Access{Implicit: true, Reg: Reg{GPR, 30}, Bits: 64}), append(vecs(0, 7, 128), vecs(16, 31, 128)...)...),
	retUses:  append([]Access{{Implicit: true, Reg: Reg{GPR, 0}, Bits: 64}, {Implicit: true, Reg: Reg{GPR, 1}, Bits: 64}, {Implicit: true, Reg: Reg{GPR, 8}, Bits: 64}, {Implicit: true, Reg: Reg{GPR, 30}, Bits: 64}}, vecs(0, 3, 128)...),
	kind: func(a asm.Instruction) (call, ret, trap, branch bool, err error) {
		switch a.Mnemonic {
		case "bl", "blr":
			return true, false, false, false, nil
		case "ret":
			return false, true, false, false, nil
		case "brk":
			return false, false, true, false, nil
		case "b", "b.", "cbz", "cbnz", "tbz", "tbnz":
			return false, false, false, true, nil
		case "br":
			return false, false, false, false, fmt.Errorf("indirect branch")
		}
		return false, false, false, false, nil
	},
	conditional: func(a asm.Instruction) bool {
		switch a.Mnemonic {
		case "cbz", "cbnz", "tbz", "tbnz", "b.":
			return true
		case "b":
			return a.Cond != ""
		}
		return false
	},
	copyOf:      arm64CopyOf,
	callerSaved: append(gprRegs(9, 17), vecRegs(16, 31)...),
	slotAccess: func(a asm.Instruction) (int, int, bool, bool) {
		if (a.Mnemonic != "ldr" && a.Mnemonic != "str") || len(a.Operands) != 2 {
			return 0, 0, false, false
		}
		reg, ok := a.Operands[0].(asm.Register)
		if !ok {
			return 0, 0, false, false
		}
		_, bits, lane, isReg, err := regOf(reg)
		if err != nil || !isReg || lane || (bits != 32 && bits != 64 && bits != 128) {
			return 0, 0, false, false
		}
		return 0, bits, a.Mnemonic == "str", true
	},
	promotable: func(class Class, bits int) bool { return bits == 32 || bits == 64 || bits == 128 },
	slotCandidates: func(class Class) []Reg {
		if class == GPR {
			return append(append(gprRegs(9, 17), gprRegs(19, 28)...), gprRegs(0, 7)...)
		}
		return append(append(vecRegs(16, 31), vecRegs(8, 15)...), vecRegs(0, 7)...)
	},
	slotCopy: arm64SlotCopy,
	clobber: func(r Reg) asm.Register {
		if r.Class == VEC {
			return asm.Register{Text: "v" + itoa(r.Num), Class: asm.ClassV, Num: r.Num, Lane: -1}
		}
		return asm.Register{Text: "x" + itoa(r.Num), Class: asm.ClassX, Num: r.Num, Lane: -1}
	},
	pure: arm64Pure,
	barrier: func(ins *Instr) bool {
		if ins.Call || ins.Ret || ins.Trap || ins.Branch {
			return true
		}
		switch ins.Asm.Mnemonic {
		case "dmb", "dsb", "isb", "ldar", "ldarb", "ldarh", "stlr", "stlrb", "stlrh", "ldxr", "ldaxr", "stxr", "stlxr", "ldxrb", "ldaxrb", "stxrb", "stlxrb", "ldxrh", "ldaxrh", "stxrh", "stlxrh", "mrs", "msr", "svc", "hint", "yield", "wfe", "wfi", "sev", "sevl":
			return true
		}
		if len(ins.Asm.Operands) > 0 {
			if r, ok := ins.Asm.Operands[0].(asm.Register); ok && r.Class == asm.ClassSP {
				return true // the frame's adjustment
			}
		}
		return false
	},
	latency: func(a asm.Instruction) int {
		switch a.Mnemonic {
		case "ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "ldrsw", "ldur", "ldp", "ld1", "ld1r":
			return 4
		case "mul", "madd", "msub", "mneg", "smull", "umull", "smulh", "umulh", "umaddl", "smaddl":
			return 3
		case "udiv", "sdiv":
			return 12
		case "fadd", "fsub", "fmul", "fmla", "fmls", "fmadd", "fmsub", "fnmadd", "fnmsub", "fcvt", "fcvtzs", "fcvtzu", "scvtf", "ucvtf", "fabs", "fneg", "fmax", "fmin":
			return 3
		case "fdiv", "fsqrt":
			return 10
		case "addv", "uaddlv", "saddlv", "umaxv", "uminv", "smaxv", "sminv", "tbl", "ext", "umov", "smov", "dup", "ins", "cmeq", "cmhi", "cmhs", "cmgt", "cmge", "cmlt", "cmle", "cmtst", "pmull", "pmull2":
			return 3
		}
		if len(a.Operands) > 0 {
			if r, ok := a.Operands[0].(asm.Register); ok && r.Class == asm.ClassV {
				return 2 // a vector ALU form
			}
		}
		return 1
	},
	writesFlags: func(a asm.Instruction) bool {
		switch a.Mnemonic {
		case "cmp", "cmn", "tst", "adds", "subs", "ands", "bics", "negs", "ccmp", "ccmn", "fcmp", "fcmpe":
			return true
		}
		return false
	},
	increment: func(a asm.Instruction) (Reg, int64, bool) {
		if (a.Mnemonic != "add" && a.Mnemonic != "sub") || len(a.Operands) != 3 {
			return Reg{}, 0, false
		}
		dst, ok1 := a.Operands[0].(asm.Register)
		src, ok2 := a.Operands[1].(asm.Register)
		imm, ok3 := a.Operands[2].(asm.Immediate)
		if !ok1 || !ok2 || !ok3 || dst.Num != src.Num || dst.Class != src.Class || (dst.Class != asm.ClassX && dst.Class != asm.ClassW) || dst.ZeroRegister() || imm.Shift != 0 {
			return Reg{}, 0, false
		}
		step := imm.Value
		if a.Mnemonic == "sub" {
			step = -step
		}
		return Reg{GPR, dst.Num}, step, true
	},
	constant: func(a asm.Instruction) (int64, bool) {
		if len(a.Operands) != 2 {
			return 0, false
		}
		switch a.Mnemonic {
		case "mov", "movz":
			if imm, ok := a.Operands[1].(asm.Immediate); ok && imm.Shift == 0 {
				return imm.Value, true
			}
			if r, ok := a.Operands[1].(asm.Register); ok && r.ZeroRegister() {
				return 0, true
			}
		}
		return 0, false
	},
	exitTest: func(a asm.Instruction) ([]Reg, int64, bool, bool) {
		if a.Mnemonic != "cmp" || len(a.Operands) != 2 {
			return nil, 0, false, false
		}
		first, ok := a.Operands[0].(asm.Register)
		if !ok || first.ZeroRegister() || (first.Class != asm.ClassX && first.Class != asm.ClassW) {
			return nil, 0, false, false
		}
		switch second := a.Operands[1].(type) {
		case asm.Register:
			if second.ZeroRegister() || (second.Class != asm.ClassX && second.Class != asm.ClassW) {
				return nil, 0, false, false
			}
			return []Reg{{GPR, first.Num}, {GPR, second.Num}}, 0, false, true
		case asm.Immediate:
			return []Reg{{GPR, first.Num}}, second.Value, true, true
		}
		return nil, 0, false, false
	},
	readsFlags: func(a asm.Instruction) bool {
		switch a.Mnemonic {
		case "csel", "cset", "csetm", "csinc", "csinv", "csneg", "cneg", "cinc", "cinv", "fcsel", "ccmp", "ccmn":
			return true
		}
		return false
	},
	frame: frameShape{
		isPairSave: func(a asm.Instruction) (int64, bool) {
			regs, off, ok := gprStore(a, "stp")
			return off, ok && len(regs) == 2 && regs[0] == (Reg{GPR, 29}) && regs[1] == (Reg{GPR, 30})
		},
		isPairRestore: func(a asm.Instruction) (int64, bool) {
			regs, off, ok := gprStore(a, "ldp")
			return off, ok && len(regs) == 2 && regs[0] == (Reg{GPR, 29}) && regs[1] == (Reg{GPR, 30})
		},
		saveOrder: gprRegs(19, 28),
		isSave: func(a asm.Instruction) ([]Reg, int64, bool) {
			regs, off, ok := gprStore(a, "stp")
			if !ok {
				regs, off, ok = gprStore(a, "str")
			}
			return regs, off, ok
		},
		save: func(r Reg, offset int64, line int) asm.Instruction {
			return asm.Instruction{Mnemonic: "str", Operands: []asm.Operand{arm64X(r.Num), spMem(offset)}, Line: line}
		},
		restore: func(r Reg, offset int64, line int) asm.Instruction {
			return asm.Instruction{Mnemonic: "ldr", Operands: []asm.Operand{arm64X(r.Num), spMem(offset)}, Line: line}
		},
		pairArea: 16,
	},
}

func arm64X(n int) asm.Register {
	return asm.Register{Text: "x" + strconv.Itoa(n), Class: asm.ClassX, Num: n, Lane: -1}
}

func spMem(offset int64) asm.Memory {
	return asm.Memory{Base: asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1}, Offset: offset}
}

// gprStore reads a store or load of general registers to the frame: the
// registers before the memory operand and the sp-relative offset.
func gprStore(a asm.Instruction, mnemonic string) ([]Reg, int64, bool) {
	if a.Mnemonic != mnemonic || len(a.Operands) < 2 {
		return nil, 0, false
	}
	m, ok := a.Operands[len(a.Operands)-1].(asm.Memory)
	if !ok || m.Base.Class != asm.ClassSP || m.Mode != asm.MemOffset || m.Index != nil {
		return nil, 0, false
	}
	var regs []Reg
	for _, op := range a.Operands[:len(a.Operands)-1] {
		reg, isReg := op.(asm.Register)
		if !isReg || (reg.Class != asm.ClassX && reg.Class != asm.ClassW && reg.Class != asm.ClassRV64X) {
			return nil, 0, false
		}
		regs = append(regs, Reg{GPR, reg.Num})
	}
	return regs, m.Offset, true
}

func gprs(from, to, bits int) []Access {
	var out []Access
	for n := from; n <= to; n++ {
		out = append(out, Access{Implicit: true, Reg: Reg{GPR, n}, Bits: bits})
	}
	return out
}

func vecs(from, to, bits int) []Access {
	var out []Access
	for n := from; n <= to; n++ {
		out = append(out, Access{Implicit: true, Reg: Reg{VEC, n}, Bits: bits})
	}
	return out
}

func fprs(from, to, bits int) []Access {
	var out []Access
	for n := from; n <= to; n++ {
		out = append(out, Access{Implicit: true, Reg: Reg{FPR, n}, Bits: bits})
	}
	return out
}

func gprRegs(from, to int) []Reg {
	var out []Reg
	for n := from; n <= to; n++ {
		out = append(out, Reg{GPR, n})
	}
	return out
}

func vecRegs(from, to int) []Reg {
	var out []Reg
	for n := from; n <= to; n++ {
		out = append(out, Reg{VEC, n})
	}
	return out
}

func fprRegs(from, to int) []Reg {
	var out []Reg
	for n := from; n <= to; n++ {
		out = append(out, Reg{FPR, n})
	}
	return out
}

// arm64CopyOf recognizes mov xD, xS / mov wD, wS; fmov dD, dS (and the
// other scalar views); mov/orr of whole vectors.
func arm64CopyOf(a asm.Instruction) (int, bool) {
	regs := func(n int) ([]asm.Register, bool) {
		if len(a.Operands) != n {
			return nil, false
		}
		out := make([]asm.Register, n)
		for i, op := range a.Operands {
			r, ok := op.(asm.Register)
			if !ok || r.Class == asm.ClassSP || r.ZeroRegister() || r.Lane >= 0 {
				return nil, false
			}
			out[i] = r
		}
		return out, true
	}
	switch a.Mnemonic {
	case "mov":
		rs, ok := regs(2)
		if !ok || rs[0].Class != rs[1].Class {
			return 0, false
		}
		switch rs[0].Class {
		case asm.ClassX, asm.ClassW:
			return viewBits(rs[0]), true
		case asm.ClassV:
			if rs[0].Vec == rs[1].Vec && (rs[0].Vec == "16b" || rs[0].Vec == "8b") {
				return viewBits(rs[0]), true
			}
		}
	case "fmov":
		rs, ok := regs(2)
		if ok && rs[0].Class == asm.ClassV && rs[1].Class == asm.ClassV && rs[0].Vec == rs[1].Vec && rs[0].Vec != "" {
			return viewBits(rs[0]), true
		}
	case "orr":
		rs, ok := regs(3)
		if ok && rs[0].Class == asm.ClassV && rs[1].Num == rs[2].Num && rs[1].Vec == rs[2].Vec && rs[0].Vec == rs[1].Vec && (rs[0].Vec == "16b" || rs[0].Vec == "8b") {
			return viewBits(rs[0]), true
		}
	}
	return 0, false
}

// arm64SlotCopy spells the copy that replaces a slot access: into the
// slot's register for a store, out of it for a load, at the slot's width.
func arm64SlotCopy(r Reg, reg asm.Register, s slot, store bool, line int) asm.Instruction {
	home := spell(reg, r)
	dst, src := home, reg
	if !store {
		dst, src = reg, home
	}
	switch {
	case s.class == GPR:
		return asm.Instruction{Mnemonic: "mov", Operands: []asm.Operand{dst, src}, Line: line}
	case s.bits == 128:
		d := asm.Register{Text: "v" + itoa(dst.Num) + ".16b", Class: asm.ClassV, Num: dst.Num, Vec: "16b", Lane: -1}
		sr := asm.Register{Text: "v" + itoa(src.Num) + ".16b", Class: asm.ClassV, Num: src.Num, Vec: "16b", Lane: -1}
		return asm.Instruction{Mnemonic: "orr", Operands: []asm.Operand{d, sr, sr}, Line: line}
	default:
		return asm.Instruction{Mnemonic: "fmov", Operands: []asm.Operand{dst, src}, Line: line}
	}
}

// ---- RV64 --------------------------------------------------------------

// rv64Names and rv64FNames spell the registers by their ABI names, as the
// lowering does.
var rv64Names = map[int]string{
	0: "zero", 1: "ra", 2: "sp", 3: "gp", 4: "tp", 5: "t0", 6: "t1", 7: "t2", 8: "s0", 9: "s1",
	10: "a0", 11: "a1", 12: "a2", 13: "a3", 14: "a4", 15: "a5", 16: "a6", 17: "a7",
	18: "s2", 19: "s3", 20: "s4", 21: "s5", 22: "s6", 23: "s7", 24: "s8", 25: "s9", 26: "s10", 27: "s11",
	28: "t3", 29: "t4", 30: "t5", 31: "t6",
}

var rv64FNames = map[int]string{
	0: "ft0", 1: "ft1", 2: "ft2", 3: "ft3", 4: "ft4", 5: "ft5", 6: "ft6", 7: "ft7",
	8: "fs0", 9: "fs1", 10: "fa0", 11: "fa1", 12: "fa2", 13: "fa3", 14: "fa4", 15: "fa5", 16: "fa6", 17: "fa7",
	18: "fs2", 19: "fs3", 20: "fs4", 21: "fs5", 22: "fs6", 23: "fs7", 24: "fs8", 25: "fs9", 26: "fs10", 27: "fs11",
	28: "ft8", 29: "ft9", 30: "ft10", 31: "ft11",
}

var rv64Shapes = map[string]shape{}

func init() {
	for _, m := range []string{
		"add", "addi", "addw", "addiw", "sub", "subw", "sll", "slli", "sllw", "slliw", "srl", "srli", "srlw", "srliw", "sra", "srai", "sraw", "sraiw",
		"and", "andi", "or", "ori", "xor", "xori", "slt", "slti", "sltu", "sltiu", "seqz", "snez", "sltz", "sgtz", "lui", "auipc", "la", "li", "mv", "not", "neg", "negw",
		"sext.w", "sext.b", "sext.h", "zext.b", "zext.h", "zext.w", "mul", "mulh", "mulhu", "mulhsu", "mulw", "div", "divu", "divw", "divuw", "rem", "remu", "remw", "remuw",
		"andn", "orn", "xnor", "min", "max", "minu", "maxu", "rol", "rolw", "ror", "rori", "rorw", "roriw", "clz", "clzw", "ctz", "ctzw", "cpop", "cpopw", "rev8", "orc.b",
		"sh1add", "sh2add", "sh3add", "sh1add.uw", "sh2add.uw", "sh3add.uw", "add.uw", "slli.uw", "bset", "bseti", "bclr", "bclri", "binv", "binvi", "bext", "bexti",
		"lb", "lh", "lw", "ld", "lbu", "lhu", "lwu", "flw", "fld",
		"fadd.s", "fadd.d", "fsub.s", "fsub.d", "fmul.s", "fmul.d", "fdiv.s", "fdiv.d", "fsqrt.s", "fsqrt.d", "fmin.s", "fmin.d", "fmax.s", "fmax.d",
		"fmadd.s", "fmadd.d", "fmsub.s", "fmsub.d", "fnmadd.s", "fnmadd.d", "fnmsub.s", "fnmsub.d",
		"fsgnj.s", "fsgnj.d", "fsgnjn.s", "fsgnjn.d", "fsgnjx.s", "fsgnjx.d", "fmv.s", "fmv.d", "fmv.x.w", "fmv.x.d", "fmv.w.x", "fmv.d.x", "fabs.s", "fabs.d", "fneg.s", "fneg.d",
		"fcvt.w.s", "fcvt.wu.s", "fcvt.l.s", "fcvt.lu.s", "fcvt.w.d", "fcvt.wu.d", "fcvt.l.d", "fcvt.lu.d", "fcvt.s.w", "fcvt.s.wu", "fcvt.s.l", "fcvt.s.lu", "fcvt.d.w", "fcvt.d.wu", "fcvt.d.l", "fcvt.d.lu", "fcvt.s.d", "fcvt.d.s",
		"feq.s", "feq.d", "flt.s", "flt.d", "fle.s", "fle.d", "fclass.s", "fclass.d",
		"vsetvli", "vsetivli",
	} {
		rv64Shapes[m] = def0
	}
	for _, m := range []string{"sb", "sh", "sw", "sd", "fsw", "fsd",
		"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz", "bgtz", "bgt", "ble", "bgtu", "bleu",
		"j", "jal", "call", "ret", "ebreak", "unimp", "fence", "fence.i", "nop"} {
		rv64Shapes[m] = noDef
	}
}

var rv64Target = &target{
	arch:   asm.ArchRV64,
	shapes: rv64Shapes,
	regOf: func(r asm.Register) (Reg, int, bool, bool, error) {
		switch r.Class {
		case asm.ClassSP:
			return Reg{}, 0, false, false, nil
		case asm.ClassRV64X:
			if r.Num == 0 {
				return Reg{}, 0, false, false, nil
			}
			if r.Num == 2 {
				return Reg{}, 0, false, false, nil // sp spelled as x2
			}
			if r.Num < 0 || r.Num > 31 {
				return Reg{}, 0, false, false, fmt.Errorf("register %s", r.Text)
			}
			return Reg{GPR, r.Num}, 64, false, true, nil
		case asm.ClassRV64F:
			if r.Num < 0 || r.Num > 31 {
				return Reg{}, 0, false, false, fmt.Errorf("register %s", r.Text)
			}
			return Reg{FPR, r.Num}, 64, false, true, nil
		}
		return Reg{}, 0, false, false, fmt.Errorf("register %s of a class the lift does not allocate", r.Text)
	},
	spell: rv64Spell,
	reserved: func(r Reg) bool {
		// ra, gp, tp; s0 is the frame pointer by convention and left alone.
		return r.Class == GPR && (r.Num == 1 || r.Num == 3 || r.Num == 4 || r.Num == 8)
	},
	calleeSaved: func(r Reg) bool {
		if r.Class != GPR && r.Class != FPR {
			return false
		}
		return r.Num == 8 || r.Num == 9 || (r.Num >= 18 && r.Num <= 27)
	},
	callUses: append(gprs(10, 17, 64), fprs(10, 17, 64)...),
	callDefs: append(append(append(append(append(gprs(1, 1, 64), gprs(5, 7, 64)...), gprs(10, 17, 64)...), gprs(28, 31, 64)...), append(fprs(0, 7, 64), fprs(10, 17, 64)...)...), fprs(28, 31, 64)...),
	retUses:  []Access{{Implicit: true, Reg: Reg{GPR, 10}, Bits: 64}, {Implicit: true, Reg: Reg{GPR, 11}, Bits: 64}, {Implicit: true, Reg: Reg{GPR, 1}, Bits: 64}, {Implicit: true, Reg: Reg{FPR, 10}, Bits: 64}, {Implicit: true, Reg: Reg{FPR, 11}, Bits: 64}},
	kind: func(a asm.Instruction) (call, ret, trap, branch bool, err error) {
		switch a.Mnemonic {
		case "call", "jal":
			return true, false, false, false, nil
		case "jalr", "jr", "tail":
			return false, false, false, false, fmt.Errorf("indirect jump %s", a.Mnemonic)
		case "ret":
			return false, true, false, false, nil
		case "ebreak", "unimp":
			return false, false, true, false, nil
		case "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz", "bgtz", "bgt", "ble", "bgtu", "bleu", "j":
			return false, false, false, true, nil
		}
		return false, false, false, false, nil
	},
	conditional: func(a asm.Instruction) bool { return a.Mnemonic != "j" },
	copyOf: func(a asm.Instruction) (int, bool) {
		if len(a.Operands) < 2 {
			return 0, false
		}
		regs := make([]asm.Register, 0, 3)
		for _, op := range a.Operands {
			r, ok := op.(asm.Register)
			if !ok || r.Class == asm.ClassSP || r.ZeroRegister() {
				return 0, false
			}
			regs = append(regs, r)
		}
		switch a.Mnemonic {
		case "mv":
			if len(regs) == 2 && regs[0].Class == asm.ClassRV64X && regs[1].Class == asm.ClassRV64X {
				return 64, true
			}
		case "fmv.d", "fmv.s":
			if len(regs) == 2 && regs[0].Class == asm.ClassRV64F && regs[1].Class == asm.ClassRV64F {
				if a.Mnemonic == "fmv.s" {
					return 32, true
				}
				return 64, true
			}
		case "fsgnj.d", "fsgnj.s":
			if len(regs) == 3 && regs[1].Num == regs[2].Num && regs[0].Class == asm.ClassRV64F {
				if a.Mnemonic == "fsgnj.s" {
					return 32, true
				}
				return 64, true
			}
		}
		return 0, false
	},
	callerSaved: append(append(gprRegs(5, 7), gprRegs(28, 31)...), append(fprRegs(0, 7), fprRegs(28, 31)...)...),
	slotAccess: func(a asm.Instruction) (int, int, bool, bool) {
		if len(a.Operands) != 2 {
			return 0, 0, false, false
		}
		switch a.Mnemonic {
		case "ld", "sd":
			if reg, ok := a.Operands[0].(asm.Register); ok && reg.Class == asm.ClassRV64X && reg.Num != 0 && reg.Num != 2 {
				return 0, 64, a.Mnemonic == "sd", true
			}
		case "fld", "fsd":
			if reg, ok := a.Operands[0].(asm.Register); ok && reg.Class == asm.ClassRV64F {
				return 0, 64, a.Mnemonic == "fsd", true
			}
		}
		return 0, 0, false, false
	},
	// Only whole words: a word stored with sw and read with lw or lwu is
	// extended on the way back, which a register copy would not do.
	promotable: func(class Class, bits int) bool { return bits == 64 },
	slotCandidates: func(class Class) []Reg {
		if class == GPR {
			return append(append(append(gprRegs(5, 7), gprRegs(28, 31)...), gprRegs(9, 9)...), append(gprRegs(18, 27), gprRegs(10, 17)...)...)
		}
		return append(append(append(fprRegs(0, 7), fprRegs(28, 31)...), fprRegs(8, 9)...), append(fprRegs(18, 27), fprRegs(10, 17)...)...)
	},
	slotCopy: func(r Reg, reg asm.Register, s slot, store bool, line int) asm.Instruction {
		home := rv64Spell(reg, r)
		dst, src := home, reg
		if !store {
			dst, src = reg, home
		}
		if s.class == FPR {
			return asm.Instruction{Mnemonic: "fmv.d", Operands: []asm.Operand{dst, src}, Line: line}
		}
		return asm.Instruction{Mnemonic: "mv", Operands: []asm.Operand{dst, src}, Line: line}
	},
	clobber: rv64Register,
	pure:    rv64Pure,
	barrier: func(ins *Instr) bool {
		if ins.Call || ins.Ret || ins.Trap || ins.Branch {
			return true
		}
		switch ins.Asm.Mnemonic {
		case "fence", "fence.i", "ecall", "ebreak", "lr.w", "lr.d", "sc.w", "sc.d", "vsetvli", "vsetivli":
			return true
		}
		if strings.HasPrefix(ins.Asm.Mnemonic, "amo") || strings.HasPrefix(ins.Asm.Mnemonic, "csr") {
			return true
		}
		if len(ins.Asm.Operands) > 0 {
			if r, ok := ins.Asm.Operands[0].(asm.Register); ok && (r.Class == asm.ClassSP || (r.Class == asm.ClassRV64X && r.Num == 2)) {
				return true
			}
		}
		return false
	},
	latency: func(a asm.Instruction) int {
		switch a.Mnemonic {
		case "lb", "lh", "lw", "ld", "lbu", "lhu", "lwu", "flw", "fld":
			return 3
		case "mul", "mulh", "mulhu", "mulhsu", "mulw":
			return 3
		case "div", "divu", "divw", "divuw", "rem", "remu", "remw", "remuw":
			return 16
		case "fadd.s", "fadd.d", "fsub.s", "fsub.d", "fmul.s", "fmul.d", "fmadd.s", "fmadd.d", "fmsub.s", "fmsub.d", "fnmadd.s", "fnmadd.d", "fnmsub.s", "fnmsub.d":
			return 4
		case "fdiv.s", "fdiv.d", "fsqrt.s", "fsqrt.d":
			return 12
		}
		return 1
	},
	writesFlags: func(asm.Instruction) bool { return false },
	increment: func(a asm.Instruction) (Reg, int64, bool) {
		if (a.Mnemonic != "addi" && a.Mnemonic != "addiw") || len(a.Operands) != 3 {
			return Reg{}, 0, false
		}
		dst, ok1 := a.Operands[0].(asm.Register)
		src, ok2 := a.Operands[1].(asm.Register)
		imm, ok3 := a.Operands[2].(asm.Immediate)
		if !ok1 || !ok2 || !ok3 || dst.Num != src.Num || dst.Class != asm.ClassRV64X || dst.Num == 0 || dst.Num == 2 {
			return Reg{}, 0, false
		}
		return Reg{GPR, dst.Num}, imm.Value, true
	},
	constant: func(a asm.Instruction) (int64, bool) {
		if len(a.Operands) != 2 {
			return 0, false
		}
		switch a.Mnemonic {
		case "li":
			if imm, ok := a.Operands[1].(asm.Immediate); ok {
				return imm.Value, true
			}
		case "mv":
			if r, ok := a.Operands[1].(asm.Register); ok && r.ZeroRegister() {
				return 0, true
			}
		}
		return 0, false
	},
	exitTest: func(a asm.Instruction) ([]Reg, int64, bool, bool) {
		switch a.Mnemonic {
		case "beq", "bne", "blt", "bge", "bltu", "bgeu", "bgt", "ble", "bgtu", "bleu":
			if len(a.Operands) != 3 {
				return nil, 0, false, false
			}
			x, ok1 := a.Operands[0].(asm.Register)
			y, ok2 := a.Operands[1].(asm.Register)
			if !ok1 || !ok2 || x.Class != asm.ClassRV64X || y.Class != asm.ClassRV64X || x.Num == 0 || y.Num == 0 {
				return nil, 0, false, false
			}
			return []Reg{{GPR, x.Num}, {GPR, y.Num}}, 0, false, true
		}
		return nil, 0, false, false
	},
	readsFlags: func(asm.Instruction) bool { return false },
	frame: frameShape{
		isPairSave: func(a asm.Instruction) (int64, bool) {
			regs, off, ok := gprStore(a, "sd")
			return off, ok && len(regs) == 1 && regs[0] == (Reg{GPR, 1})
		},
		isPairRestore: func(a asm.Instruction) (int64, bool) {
			regs, off, ok := gprStore(a, "ld")
			return off, ok && len(regs) == 1 && regs[0] == (Reg{GPR, 1})
		},
		// The lowering's variable homes: s1, then s2–s11 (s0 stays the
		// frame pointer's).
		saveOrder: append([]Reg{{GPR, 9}}, gprRegs(18, 27)...),
		isSave: func(a asm.Instruction) ([]Reg, int64, bool) {
			regs, off, ok := gprStore(a, "sd")
			if !ok || len(regs) != 1 || regs[0].Num == 1 {
				return nil, 0, false
			}
			return regs, off, true
		},
		save: func(r Reg, offset int64, line int) asm.Instruction {
			return asm.Instruction{Mnemonic: "sd", Operands: []asm.Operand{rv64Register(r), spMem(offset)}, Line: line}
		},
		restore: func(r Reg, offset int64, line int) asm.Instruction {
			return asm.Instruction{Mnemonic: "ld", Operands: []asm.Operand{rv64Register(r), spMem(offset)}, Line: line}
		},
		pairArea: 16,
	},
}

// rv64Spell rewrites a register operand to a physical register by its ABI
// name.
func rv64Spell(r asm.Register, to Reg) asm.Register {
	out := r
	out.Num = to.Num
	if r.Class == asm.ClassRV64F {
		out.Text = rv64FNames[to.Num]
	} else {
		out.Text = rv64Names[to.Num]
	}
	return out
}

// rv64Register spells a register operand.
func rv64Register(r Reg) asm.Register {
	if r.Class == FPR {
		return asm.Register{Text: rv64FNames[r.Num], Class: asm.ClassRV64F, Num: r.Num, Lane: -1}
	}
	return asm.Register{Text: rv64Names[r.Num], Class: asm.ClassRV64X, Num: r.Num, Lane: -1}
}

// frameLoad reports a load whose only memory operand is sp-relative.
func frameLoad(a asm.Instruction) bool {
	for _, op := range a.Operands {
		if m, ok := op.(asm.Memory); ok {
			return m.Base.Class == asm.ClassSP && m.Mode == asm.MemOffset && m.Index == nil
		}
	}
	return false
}

var arm64PureSet = map[string]bool{}
var rv64PureSet = map[string]bool{}

func init() {
	for _, m := range []string{"mov", "movz", "movk", "movn", "mvn", "neg", "add", "sub", "mul", "madd", "msub", "mneg", "smull", "umull", "smulh", "umulh", "umaddl", "smaddl", "udiv", "sdiv",
		"and", "orr", "eor", "bic", "orn", "eon", "lsl", "lsr", "asr", "ror", "clz", "cls", "rbit", "cnt", "rev", "rev16", "rev32", "rev64", "sxtb", "sxth", "sxtw", "uxtb", "uxth", "ubfx", "sbfx", "ubfiz", "sbfiz", "extr",
		"csel", "cset", "csetm", "csinc", "csinv", "csneg", "cneg", "cinc", "cinv", "adr", "adrp", "adrl",
		"fmov", "fadd", "fsub", "fmul", "fdiv", "fneg", "fabs", "fsqrt", "fmax", "fmin", "fmaxnm", "fminnm", "fmadd", "fmsub", "fnmadd", "fnmsub", "fnmul", "fcvt", "fcvtzs", "fcvtzu", "scvtf", "ucvtf", "frintz", "frintm", "frintp", "frinta", "frintn", "frintx", "fcsel",
		"dup", "movi", "mvni", "ext", "tbl", "cmeq", "cmhi", "cmhs", "cmgt", "cmge", "cmle", "cmlt", "cmtst", "fcmeq", "fcmgt", "fcmge", "addv", "uaddlv", "saddlv", "umaxv", "uminv", "smaxv", "sminv", "umov", "smov",
		"shl", "sshr", "ushr", "sshl", "ushl", "shrn", "sshll", "ushll", "uxtl", "sxtl", "xtn", "uqxtn", "sqxtn", "uzp1", "uzp2", "zip1", "zip2", "trn1", "trn2", "addp", "faddp", "umax", "umin", "smax", "smin",
		"uaddl", "uaddw", "usubl", "usubw", "abs", "sqadd", "uqadd", "sqsub", "uqsub", "not", "fmla", "fmls", "mla", "mls", "bsl", "bit", "bif", "ins", "umlal", "smlal", "sadalp", "uadalp", "bfi", "bfxil", "sli", "sri", "pmul", "pmull", "pmull2", "uabd", "sabd", "fabd"} {
		arm64PureSet[m] = true
	}
	for _, m := range []string{"add", "addi", "addw", "addiw", "sub", "subw", "sll", "slli", "sllw", "slliw", "srl", "srli", "srlw", "srliw", "sra", "srai", "sraw", "sraiw",
		"and", "andi", "or", "ori", "xor", "xori", "slt", "slti", "sltu", "sltiu", "seqz", "snez", "sltz", "sgtz", "lui", "auipc", "la", "li", "mv", "not", "neg", "negw",
		"sext.w", "sext.b", "sext.h", "zext.b", "zext.h", "zext.w", "mul", "mulh", "mulhu", "mulhsu", "mulw", "div", "divu", "divw", "divuw", "rem", "remu", "remw", "remuw",
		"andn", "orn", "xnor", "min", "max", "minu", "maxu", "rol", "rolw", "ror", "rori", "rorw", "roriw", "clz", "clzw", "ctz", "ctzw", "cpop", "cpopw", "rev8", "orc.b",
		"sh1add", "sh2add", "sh3add", "sh1add.uw", "sh2add.uw", "sh3add.uw", "add.uw", "slli.uw",
		"fadd.s", "fadd.d", "fsub.s", "fsub.d", "fmul.s", "fmul.d", "fdiv.s", "fdiv.d", "fsqrt.s", "fsqrt.d", "fmin.s", "fmin.d", "fmax.s", "fmax.d",
		"fmadd.s", "fmadd.d", "fmsub.s", "fmsub.d", "fnmadd.s", "fnmadd.d", "fnmsub.s", "fnmsub.d", "fsgnj.s", "fsgnj.d", "fsgnjn.s", "fsgnjn.d", "fsgnjx.s", "fsgnjx.d",
		"fmv.s", "fmv.d", "fmv.x.w", "fmv.x.d", "fmv.w.x", "fmv.d.x", "fabs.s", "fabs.d", "fneg.s", "fneg.d", "fcvt.s.d", "fcvt.d.s", "fclass.s", "fclass.d"} {
		rv64PureSet[m] = true
	}
}

// arm64Pure: the ALU, move, and vector forms that set no flags, and loads
// from the frame.
func arm64Pure(a asm.Instruction) bool {
	if arm64PureSet[a.Mnemonic] {
		return true
	}
	switch a.Mnemonic {
	case "ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "ldrsw", "ldur", "ldp":
		return frameLoad(a)
	}
	return false
}

// rv64Pure: the ALU, move, and floating forms (RISC-V integer division
// and conversions do not trap), and loads from the frame.
func rv64Pure(a asm.Instruction) bool {
	if rv64PureSet[a.Mnemonic] {
		return true
	}
	switch a.Mnemonic {
	case "lb", "lh", "lw", "ld", "lbu", "lhu", "lwu", "flw", "fld":
		return frameLoad(a)
	}
	return false
}
