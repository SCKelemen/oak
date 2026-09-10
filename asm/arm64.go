package asm

// The v1 AArch64 instruction table (docs/spec/94-assembler.md §3–§4): each
// entry states its legal operand forms, its flag effects, whether it
// touches memory, its branch kind, and whether it needs the unit's
// `system` capability. Everything not in the table is not expressible —
// no raw encodings, no undeclared side effects.

type branchKind int

const (
	branchNone branchKind = iota
	branchUnconditional
	branchConditional
	branchCall
	branchReturn
)

type instructionSpec struct {
	forms         []form
	setsFlags     bool
	readsFlags    bool
	system        bool
	barrier       bool
	branch        branchKind
	memory        bool
	sysregOperand int // operand position that names a system register, -1 if none
	// clobbersCallerSaved marks bl: x0–x17 and the flags are unknown after
	// the call (the callee owns them under AAPCS64).
	clobbersCallerSaved bool
}

// form is one legal operand shape; each entry is an operand class.
type form []operandClass

type operandClass int

const (
	opX      operandClass = iota // arm64.X register
	opW                          // arm64.W register
	opV                          // arm64.V register
	opSP                         // sp
	opImm                        // #immediate
	opMem                        // [base, #off] with sp base
	opSym                        // label or Oak function symbol
	opSysReg                     // system register name
	opOption                     // barrier option
	opCond                       // condition code operand of csel/cset
	opNone                       // no operands
)

var conditionCodes = map[string]bool{
	"eq": true, "ne": true, "cs": true, "hs": true, "cc": true, "lo": true,
	"mi": true, "pl": true, "vs": true, "vc": true, "hi": true, "ls": true,
	"ge": true, "lt": true, "gt": true, "le": true, "al": true,
}

func regForms3() []form {
	return []form{{opX, opX, opX}, {opW, opW, opW}, {opX, opX, opImm}, {opW, opW, opImm}}
}

var instructionTable = map[string]instructionSpec{
	"mov":  {forms: []form{{opX, opX}, {opW, opW}, {opX, opImm}, {opW, opImm}, {opX, opSP}, {opSP, opX}}, sysregOperand: -1},
	"add":  {forms: append(regForms3(), form{opSP, opSP, opImm}), sysregOperand: -1},
	"sub":  {forms: append(regForms3(), form{opSP, opSP, opImm}), sysregOperand: -1},
	"adds": {forms: regForms3(), setsFlags: true, sysregOperand: -1},
	"subs": {forms: regForms3(), setsFlags: true, sysregOperand: -1},
	"and":  {forms: regForms3(), sysregOperand: -1},
	"orr":  {forms: regForms3(), sysregOperand: -1},
	"eor":  {forms: regForms3(), sysregOperand: -1},
	"lsl":  {forms: []form{{opX, opX, opImm}, {opW, opW, opImm}, {opX, opX, opX}, {opW, opW, opW}}, sysregOperand: -1},
	"lsr":  {forms: []form{{opX, opX, opImm}, {opW, opW, opImm}, {opX, opX, opX}, {opW, opW, opW}}, sysregOperand: -1},
	"cmp":  {forms: []form{{opX, opX}, {opW, opW}, {opX, opImm}, {opW, opImm}}, setsFlags: true, sysregOperand: -1},
	"csel": {forms: []form{{opX, opX, opX, opCond}, {opW, opW, opW, opCond}}, readsFlags: true, sysregOperand: -1},
	"cset": {forms: []form{{opX, opCond}, {opW, opCond}}, readsFlags: true, sysregOperand: -1},
	"ldr":  {forms: []form{{opX, opMem}, {opW, opMem}}, memory: true, sysregOperand: -1},
	"str":  {forms: []form{{opX, opMem}, {opW, opMem}}, memory: true, sysregOperand: -1},
	"ldrb": {forms: []form{{opW, opMem}}, memory: true, sysregOperand: -1},
	"ldrh": {forms: []form{{opW, opMem}}, memory: true, sysregOperand: -1},
	"strb": {forms: []form{{opW, opMem}}, memory: true, sysregOperand: -1},
	"strh": {forms: []form{{opW, opMem}}, memory: true, sysregOperand: -1},
	"mul":  {forms: []form{{opX, opX, opX}, {opW, opW, opW}}, sysregOperand: -1},
	"neg":  {forms: []form{{opX, opX}, {opW, opW}}, sysregOperand: -1},
	"mvn":  {forms: []form{{opX, opX}, {opW, opW}}, sysregOperand: -1},
	"asr":  {forms: []form{{opX, opX, opImm}, {opW, opW, opImm}, {opX, opX, opX}, {opW, opW, opW}}, sysregOperand: -1},
	"tst":  {forms: []form{{opX, opX}, {opW, opW}, {opX, opImm}, {opW, opImm}}, setsFlags: true, sysregOperand: -1},
	"ldp":  {forms: []form{{opX, opX, opMem}, {opW, opW, opMem}}, memory: true, sysregOperand: -1},
	"stp":  {forms: []form{{opX, opX, opMem}, {opW, opW, opMem}}, memory: true, sysregOperand: -1},
	"b":    {forms: []form{{opSym}}, branch: branchUnconditional, sysregOperand: -1},
	"b.":   {forms: []form{{opSym}}, branch: branchConditional, readsFlags: true, sysregOperand: -1},
	"cbz":  {forms: []form{{opW, opSym}, {opX, opSym}}, branch: branchConditional, sysregOperand: -1},
	"cbnz": {forms: []form{{opW, opSym}, {opX, opSym}}, branch: branchConditional, sysregOperand: -1},
	"tbz":  {forms: []form{{opW, opImm, opSym}, {opX, opImm, opSym}}, branch: branchConditional, sysregOperand: -1},
	"tbnz": {forms: []form{{opW, opImm, opSym}, {opX, opImm, opSym}}, branch: branchConditional, sysregOperand: -1},
	"bl":   {forms: []form{{opSym}}, branch: branchCall, clobbersCallerSaved: true, sysregOperand: -1},
	"ret":  {forms: []form{{opNone}}, branch: branchReturn, sysregOperand: -1},
	"eret": {forms: []form{{opNone}}, branch: branchReturn, system: true, sysregOperand: -1},
	"mrs":  {forms: []form{{opX, opSysReg}}, system: true, sysregOperand: 1},
	"msr":  {forms: []form{{opSysReg, opX}}, system: true, sysregOperand: 0},
	"dmb":  {forms: []form{{opOption}}, barrier: true, sysregOperand: -1},
	"dsb":  {forms: []form{{opOption}}, barrier: true, sysregOperand: -1},
	"isb":  {forms: []form{{opOption}, {opNone}}, barrier: true, sysregOperand: -1},
	"nop":  {forms: []form{{opNone}}, sysregOperand: -1},
}

// matchForm reports whether the operands fit any legal form, returning the
// matched form for width discipline.
func matchForm(spec instructionSpec, operands []Operand) (form, bool) {
	for _, candidate := range spec.forms {
		if len(candidate) == 1 && candidate[0] == opNone {
			if len(operands) == 0 {
				return candidate, true
			}
			continue
		}
		if len(candidate) != len(operands) {
			continue
		}
		matched := true
		for i, class := range candidate {
			if !operandMatches(class, operands[i]) {
				matched = false
				break
			}
		}
		if matched {
			return candidate, true
		}
	}
	return nil, false
}

func operandMatches(class operandClass, operand Operand) bool {
	switch class {
	case opX:
		reg, ok := operand.(Register)
		return ok && reg.Class == ClassX
	case opW:
		reg, ok := operand.(Register)
		return ok && reg.Class == ClassW
	case opV:
		reg, ok := operand.(Register)
		return ok && reg.Class == ClassV
	case opSP:
		reg, ok := operand.(Register)
		return ok && reg.Class == ClassSP
	case opImm:
		_, ok := operand.(Immediate)
		return ok
	case opMem:
		_, ok := operand.(Memory)
		return ok
	case opSym:
		_, ok := operand.(Symbol)
		return ok
	case opSysReg:
		_, ok := operand.(SysReg)
		return ok
	case opOption:
		_, ok := operand.(Option)
		return ok
	case opCond:
		_, ok := operand.(Condition)
		return ok
	}
	return false
}

// accessBytes is the memory footprint of one load/store form.
func accessBytes(mnemonic string, class operandClass) int64 {
	switch mnemonic {
	case "ldrb", "strb":
		return 1
	case "ldrh", "strh":
		return 2
	}
	width := int64(8)
	if class == opW {
		width = 4
	}
	if mnemonic == "ldp" || mnemonic == "stp" {
		return 2 * width
	}
	return width
}
