package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// The RV64 lane of the verifier (docs/spec/94-assembler.md §8, §9): the
// same term language, path executor, and equality decision as the
// AArch64 lane, with the ISA's semantics for each instruction. Every
// register is a 64-bit term; the W-forms compute at 32 bits and
// sign-extend (Oak.RiscV.addw and its kin); slt/sltu are comparison terms;
// a conditional branch is a comparison of two registers, so the
// comparison-branch condition is the same cmpTerm the flags produced on
// AArch64 (Oak.RiscV.brHolds_eq_condHolds bridges the two). Division and
// remainder carry RISC-V's total semantics (rv.div and its kin in
// evalBinaryExtra). auipc, calls, and memory through any base but sp are
// outside the verified subset: the unit stays checked and trusted.

// rv64BranchCodes maps a conditional branch to the AArch64 condition code
// of the same comparison: the term is the same, the ISA's reading differs.
var rv64BranchCodes = map[string]string{"beq": "eq", "bne": "ne", "blt": "lt", "bge": "ge", "bltu": "lo", "bgeu": "hs"}

// rv64ConditionalBranches are the branch spellings the executor forks on,
// pseudo forms included (the executor sees the unit's spelling).
var rv64ConditionalBranches = map[string]bool{"beq": true, "bne": true, "blt": true, "bge": true, "bltu": true, "bgeu": true, "beqz": true, "bnez": true, "bgez": true, "bltz": true, "blez": true, "bgtz": true}

// bindRV64Params places the parameters in their LP64 registers as terms.
// The psABI widens an integer scalar narrower than XLEN by its own sign to
// 32 bits, then sign-extends to 64: the bits above a narrow parameter are
// determined, unlike AAPCS64's unspecified upper half.
func bindRV64Params(fn *Function, sig *ast.FunctionStatement, state *symbolicState, input func(string, int) *term, spans map[string]int64, declared map[string]int) (string, bool) {
	for _, param := range sig.Parameters {
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			spans[param.Name.Value] = elem
			declared[spanLenName(param.Name.Value)] = 32
			declared[spanBaseName(param.Name.Value)] = 64
			continue
		}
		bits, _, ok := contractBits(param.Type)
		if !ok {
			return "vector or non-integer parameters", false
		}
		declared[param.Name.Value] = bits
	}
	for _, binding := range fn.Bindings {
		if binding.Length != nil {
			if _, isSpan := spans[binding.Param]; !isSpan {
				return "span binding of a non-span parameter", false
			}
			state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
			state.regs[binding.Length.Num] = zeroExtend(input(spanLenName(binding.Param), 32), 64)
			continue
		}
		bits := declared[binding.Param]
		_, signed, _ := contractBits(sigParamType(sig, binding.Param))
		value := zeroExtend(input(binding.Param, bits), 64)
		switch {
		case bits == 64:
		case signed:
			value = extendTerm(value, bits, 64, true)
		case bits == 32:
			value = extendTerm(value, 32, 64, true)
		}
		state.regs[binding.Register.Num] = value
	}
	return "", true
}

func sigParamType(sig *ast.FunctionStatement, name string) ast.Expression {
	for _, param := range sig.Parameters {
		if param.Name.Value == name {
			return param.Type
		}
	}
	return nil
}

// rv64ResultRegister is a0 as the executor's ret reads it.
var rv64ResultRegister = Register{Text: "a0", Class: ClassRV64X, Num: 10, Lane: -1}

// rv64BranchCondition is the comparison a conditional branch tests.
func rv64BranchCondition(instr Instruction, state *symbolicState) (*term, string, bool) {
	base := rv64Base(instr)
	code, isBranch := rv64BranchCodes[base.Mnemonic]
	if !isBranch {
		return nil, fmt.Sprintf("instruction %s", instr.Mnemonic), false
	}
	left, okL := state.read(base.Operands[0].(Register))
	right, okR := state.read(base.Operands[1].(Register))
	if !okL || !okR {
		return nil, "unbound register read", false
	}
	return cmpTerm(code, left, right), "", true
}

var rv64ALU = map[string]string{"add": "add", "sub": "sub", "and": "and", "or": "or", "xor": "xor", "sll": "shl", "srl": "shr", "sra": "sar", "mul": "mul",
	"div": "rv.div", "divu": "rv.divu", "rem": "rv.rem", "remu": "rv.remu", "mulhu": "umulh", "mulh": "smulh"}
var rv64ALUImm = map[string]string{"addi": "add", "andi": "and", "ori": "or", "xori": "xor", "slli": "shl", "srli": "shr", "srai": "sar"}
var rv64ALUW = map[string]string{"addw": "add", "subw": "sub", "sllw": "shl", "srlw": "shr", "sraw": "sar", "mulw": "mul", "divw": "rv.div", "divuw": "rv.divu", "remw": "rv.rem", "remuw": "rv.remu"}
var rv64ALUImmW = map[string]string{"addiw": "add", "slliw": "shl", "srliw": "shr", "sraiw": "sar"}

// stepRV64 executes one non-control instruction.
func (x *pathExecutor) stepRV64(instr Instruction, state *symbolicState) (string, bool) {
	for _, operand := range instr.Operands {
		if reg, isReg := operand.(Register); isReg && reg.Class == ClassRV64F {
			return "a floating-point instruction (" + instr.Mnemonic + ")", false
		}
	}
	if instr.Mnemonic == "li" {
		// One constant, however many words the encoder spends on it.
		state.write(instr.Operands[0].(Register), constTerm(uint64(instr.Operands[1].(Immediate).Value), 64))
		return "", true
	}
	base := rv64Base(instr)
	ops := base.Operands
	name := base.Mnemonic
	reg := func(i int) Register { return ops[i].(Register) }
	read := func(i int) (*term, bool) { return state.read(reg(i)) }
	imm := func(i int, width int) *term { return constTerm(uint64(ops[i].(Immediate).Value), width) }
	if op, isALU := rv64ALU[name]; isALU {
		l, okL := read(1)
		r, okR := read(2)
		if !okL || !okR {
			return "unbound register read", false
		}
		state.write(reg(0), binaryTerm(op, l, r))
		return "", true
	}
	if op, isALU := rv64ALUImm[name]; isALU {
		if reg(0).Class == ClassSP {
			// addi sp, sp, imm: the frame moves (the checker bounded it).
			state.disp -= ops[2].(Immediate).Value
			return "", true
		}
		l, ok := read(1)
		if !ok {
			return "unbound register read", false
		}
		if name == "srli" && ops[2].(Immediate).Value == 32 && l.kind == termBinary && l.op == "shl" && l.right.kind == termConst && l.right.value == 32 {
			// (x << 32) >> 32 is the zero extension of x's low half
			// (Oak.RiscV.normalize_eq): the checker's length normalization,
			// folded so a normalized length is the length's own term.
			state.write(reg(0), zeroExtend(truncate(l.left, 32), 64))
			return "", true
		}
		state.write(reg(0), binaryTerm(op, l, imm(2, 64)))
		return "", true
	}
	if op, isALU := rv64ALUW[name]; isALU {
		l, okL := read(1)
		r, okR := read(2)
		if !okL || !okR {
			return "unbound register read", false
		}
		state.write(reg(0), extendTerm(binaryTerm(op, truncate(l, 32), truncate(r, 32)), 32, 64, true))
		return "", true
	}
	if op, isALU := rv64ALUImmW[name]; isALU {
		l, ok := read(1)
		if !ok {
			return "unbound register read", false
		}
		state.write(reg(0), extendTerm(binaryTerm(op, truncate(l, 32), imm(2, 32)), 32, 64, true))
		return "", true
	}
	switch name {
	case "slt", "sltu", "slti", "sltiu":
		l, ok := read(1)
		if !ok {
			return "unbound register read", false
		}
		var r *term
		if name == "slt" || name == "sltu" {
			if r, ok = read(2); !ok {
				return "unbound register read", false
			}
		} else {
			r = imm(2, 64)
		}
		code := "lt"
		if name == "sltu" || name == "sltiu" {
			code = "lo"
		}
		state.write(reg(0), cmpTerm(code, l, r))
		return "", true
	case "lui":
		state.write(reg(0), constTerm(uint64(ops[1].(Immediate).Value<<12), 64))
		return "", true
	case "auipc":
		return "a pc-relative address (auipc)", false
	case "jal", "jalr", "call":
		return "a call", false
	}
	if width, isLoad := rv64Loads[name]; isLoad {
		if ops[1].(Memory).Base.Class != ClassSP {
			return x.spanLoadRV64(reg(0), ops[1].(Memory), width, name, state)
		}
		return x.frameAccessRV64(reg(0), ops[1].(Memory), width, name, false, state)
	}
	if width, isStore := rv64Stores[name]; isStore {
		if ops[1].(Memory).Base.Class != ClassSP {
			return "a store through a span (the verifier decides results, not memory effects)", false
		}
		return x.frameAccessRV64(reg(0), ops[1].(Memory), width, name, true, state)
	}
	return "instruction " + instr.Mnemonic, false
}

// spanLoadRV64 resolves a load through a span base to the element it
// reads: the address is `&v + K` (a constant offset, K a multiple of the
// element size) or `&v + (idx << s)` with 2^s the element size — the
// checker's guarded-index idiom (docs/spec/94-assembler.md §9). The load
// width is the element width; lw/lh/lb sign-extend, lwu/lhu/lbu zero-extend.
func (x *pathExecutor) spanLoadRV64(dest Register, mem Memory, width int, name string, state *symbolicState) (string, bool) {
	address, bound := state.regs[mem.Base.Num]
	if !bound {
		return "a load through a register that is not a span base", false
	}
	var span string
	var index *term
	if param, offset, isBase := spanBaseOf(address); isBase {
		elem := x.spans[param]
		offset += mem.Offset
		if elem == 0 || offset%elem != 0 || offset < 0 {
			return "a span offset not aligned to an element", false
		}
		span, index = param, constTerm(uint64(offset/elem), 32)
	} else if address.kind == termBinary && address.op == "add" {
		// &v + (idx << s), either order.
		base, scaled := address.left, address.right
		if _, _, isBase := spanBaseOf(base); !isBase {
			base, scaled = address.right, address.left
		}
		param, offset, isBase := spanBaseOf(base)
		if !isBase || offset != 0 || mem.Offset != 0 {
			return "a load through an address that is not a span element", false
		}
		if scaled.kind != termBinary || scaled.op != "shl" || scaled.right.kind != termConst || int64(1)<<scaled.right.value != x.spans[param] {
			return "an element address whose scale is not the element size", false
		}
		span, index = param, scaled.left
	} else {
		return "a load through a register that is not a span base", false
	}
	if int64(width) != x.spans[span] {
		return fmt.Sprintf("a %d-byte load over %d-byte elements", width, x.spans[span]), false
	}
	element := x.element(span, index, width*8)
	value := zeroExtend(element, 64)
	switch name {
	case "lw", "lh", "lb":
		value = extendTerm(value, width*8, 64, true)
	}
	state.write(dest, value)
	return "", true
}

// frameAccessRV64 executes a load or store through the sp frame: the
// address is entry-relative (-disp + offset) as the checker computes it;
// a store records the value at its width, a load reads back a slot stored
// at the same width and extends it as the load spells.
func (x *pathExecutor) frameAccessRV64(reg Register, mem Memory, width int, name string, store bool, state *symbolicState) (string, bool) {
	if mem.Base.Class != ClassSP {
		return "memory through a register other than sp", false
	}
	addr := -state.disp + mem.Offset
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	if store {
		value, ok := state.read(reg)
		if !ok {
			return "unbound register read", false
		}
		state.frame[addr] = frameSlot{value: truncate(value, 8*width), width: width}
		return "", true
	}
	slot, stored := state.frame[addr]
	if !stored {
		return "a load from a frame slot never stored on this path", false
	}
	if slot.width != width {
		return "a load whose width differs from the slot's store", false
	}
	value := zeroExtend(slot.value, 64)
	switch name {
	case "lw", "lh", "lb":
		value = extendTerm(value, 8*width, 64, true)
	}
	state.write(reg, value)
	return "", true
}
