package asm

import (
	"fmt"
	"strings"

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
// determined, unlike AAPCS64's unspecified upper half. A record or union
// parameter arrives as its leaves: up to 16 bytes as one or two register
// chunks assembled from them (a0, a1), beyond that by reference to the
// caller's copy, loads through which read the leaves (spanLoadRV64).
func bindRV64Params(fn *Function, sig *ast.FunctionStatement, state *symbolicState, input func(string, int) *term, spans map[string]int64, declared map[string]int, composites map[string]compositeArg) (string, bool) {
	for _, param := range sig.Parameters {
		if comp, isComposite := fn.Composites[typeText(param.Type)]; isComposite && len(comp.Fields) > 0 {
			leaves, reason, ok := compositeLeaves(fn.Composites, typeText(param.Type), param.Name.Value, 0, nil)
			if !ok {
				return reason, false
			}
			for _, leaf := range leaves {
				declared[leaf.name] = leaf.width
			}
			composites[param.Name.Value] = compositeArg{leaves: leaves, size: comp.Size}
			if comp.Size > 16 {
				declared[spanBaseName(param.Name.Value)] = 64
			}
			continue
		}
		if elem, _, isSpan := spanShape(param.Type); isSpan {
			spans[param.Name.Value] = elem
			declared[spanLenName(param.Name.Value)] = 32
			declared[spanBaseName(param.Name.Value)] = 64
			continue
		}
		if shape, isVector := vectorShape(param.Type); isVector {
			// A fixed vector: its lanes are the leaves `p[k]`, the register
			// (v8–v23) the whole (asm/verify_vector.go).
			for k := 0; k < shape.Lanes; k++ {
				declared[spanElemName(param.Name.Value, int64(k))] = laneWidth(shape)
			}
			continue
		}
		bits, _, ok := contractBits(param.Type)
		if !ok {
			return "vector or non-integer parameters", false
		}
		declared[param.Name.Value] = bits
	}
	for _, binding := range fn.Bindings {
		if binding.OnStack {
			return "parameters beyond the register contract (the incoming stack area is not modeled)", false
		}
		if cp, isComposite := composites[binding.Param]; isComposite {
			if cp.size > 16 {
				state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
				continue
			}
			state.regs[binding.Register.Num] = chunkTerm(cp.leaves, 0, input)
			if binding.Length != nil {
				state.regs[binding.Length.Num] = chunkTerm(cp.leaves, 1, input)
			}
			continue
		}
		if binding.Length != nil {
			if _, isSpan := spans[binding.Param]; !isSpan {
				return "span binding of a non-span parameter", false
			}
			state.regs[binding.Register.Num] = paramTerm(spanBaseName(binding.Param), 64)
			// The length is a u32 argument, widened like any other
			// (Oak.RiscV.widen): a raw comparison of two widened u32s is
			// their 32-bit comparison (Oak.RiscV.index_guard_widened).
			state.regs[binding.Length.Num] = extendTerm(zeroExtend(input(spanLenName(binding.Param), 32), 64), 32, 64, true)
			continue
		}
		bits := declared[binding.Param]
		if binding.Register.Class == ClassRV64F {
			// f32/f64 under LP64D: the pattern at its width in fa0–fa7.
			state.write(binding.Register, input(binding.Param, bits))
			continue
		}
		if binding.Register.Class == ClassRV64V {
			shape, isVector := vectorShape(sigParamType(sig, binding.Param))
			if !isVector {
				return "a vector register bound to a non-vector parameter", false
			}
			state.writeVec(binding.Register.Num, vectorParamValue(binding.Param, shape, input))
			continue
		}
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

// rv64ResultRegister is a0 as the executor's ret reads it; an f32/f64
// result is fa0 (LP64D); a fixed vector result is v8 (the RVV psABI).
var rv64ResultRegister = Register{Text: "a0", Class: ClassRV64X, Num: 10, Lane: -1}
var rv64FloatResultRegister = Register{Text: "fa0", Class: ClassRV64F, Num: 10, Lane: -1}

const rv64VectorResultRegister = 8

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

// rv64ALUTerm builds an ALU result; the M extension's division and
// remainder are the uninterpreted quotient (asm/floats_ops.go) and
// a - (a / b) * b, RISC-V's definition of rem (unprivileged spec §7.2;
// Oak.IntegerDivision), so an RV64 unit and a NEON unit decide against
// one term.
func rv64ALUTerm(op string, l, r *term, width int) *term {
	switch op {
	case "rv.div":
		return floatTerm("rv.sdiv", width, l, r)
	case "rv.divu":
		return floatTerm("rv.udiv", width, l, r)
	case "rv.rem":
		return binaryTerm("sub", l, binaryTerm("mul", floatTerm("rv.sdiv", width, l, r), r))
	case "rv.remu":
		return binaryTerm("sub", l, binaryTerm("mul", floatTerm("rv.udiv", width, l, r), r))
	}
	return binaryTerm(op, l, r)
}

var rv64ALUW = map[string]string{"addw": "add", "subw": "sub", "sllw": "shl", "srlw": "shr", "sraw": "sar", "mulw": "mul", "divw": "rv.div", "divuw": "rv.divu", "remw": "rv.rem", "remuw": "rv.remu"}
var rv64ALUImmW = map[string]string{"addiw": "add", "slliw": "shl", "srliw": "shr", "sraiw": "sar"}

// stepRV64 executes one non-control instruction.
func (x *pathExecutor) stepRV64(instr Instruction, state *symbolicState) (string, bool) {
	if rv64VectorShapes[instr.Mnemonic] != "" {
		// The vector file under a fixed configuration (asm/rv64_verify_vector.go);
		// vfmv.v.f/vfmv.f.s cross into the floating-point file from here.
		return x.stepRV64Vector(instr, state)
	}
	for _, operand := range instr.Operands {
		if reg, isReg := operand.(Register); isReg && reg.Class == ClassRV64F {
			return x.stepRV64Float(instr, state)
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
		state.write(reg(0), rv64ALUTerm(op, l, r, 64))
		return "", true
	}
	if op, isALU := rv64ALUImm[name]; isALU {
		if reg(0).Class == ClassSP {
			// addi sp, sp, imm: the frame moves (the checker bounded it).
			state.disp -= ops[2].(Immediate).Value
			return "", true
		}
		if reg(1).Class == ClassSP {
			// `addi rD, sp, imm`: rD holds a frame address (a fixed vector's
			// spill slot, asm/rv64_verify_vector.go); a scalar access
			// through it stays outside the model.
			state.write(reg(0), rvFrameAddrTerm(-state.disp+ops[2].(Immediate).Value))
			return "", true
		}
		l, ok := read(1)
		if !ok {
			return "unbound register read", false
		}
		if count := ops[2].(Immediate).Value; name == "srli" && count >= 1 && count <= 32 && l.kind == termBinary && l.op == "shl" && l.right.kind == termConst && l.right.value == 32 {
			// (x << 32) >> 32 is the zero extension of x's low half
			// (Oak.RiscV.normalize_eq): the checker's length normalization,
			// folded so a normalized length is the length's own term; and
			// (x << 32) >> (32 - s) is that zero extension shifted by s
			// (Oak.RiscV.widened_scale): GCC's fused zero-extend-and-scale
			// of an index, folded to the element shape `idx << s`.
			low := zeroExtend(truncate(l.left, 32), 64)
			if count < 32 {
				low = binaryTerm("shl", low, constTerm(uint64(32-count), 64))
			}
			state.write(reg(0), low)
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
		state.write(reg(0), extendTerm(rv64ALUTerm(op, truncate(l, 32), truncate(r, 32), 32), 32, 64, true))
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
	case "la":
		// A constant table's address is the base of the span its Oak name
		// denotes (executeBodyChunk); a package global's address is the
		// distinguished parameter the loads and stores below recognize
		// (docs/spec/94-assembler.md §9).
		sym, isSym := ops[1].(Symbol)
		if !isSym {
			return "la without a symbol", false
		}
		if x.fn != nil {
			if _, known := x.fn.Tables[sym.Name]; known {
				state.write(reg(0), paramTerm(spanBaseName(TableName(sym.Name)), 64))
				return "", true
			}
		}
		if _, isGlobal := x.globals[sym.Name]; !isGlobal {
			return "la of a symbol that is neither a constant table nor a package global", false
		}
		state.write(reg(0), paramTerm(globalAddrName(sym.Name), 64))
		return "", true
	case "auipc":
		return "a pc-relative address (auipc)", false
	case "call":
		// The summary reads the vector arguments, then forgets the vector
		// file and its configuration (caller-saved under the psABI) and
		// writes a vector result to v8.
		return x.summarizeCall(instr, state)
	case "jal", "jalr":
		return "a call", false
	}
	if kind, width, isAtomic := rv64Atomic(name); isAtomic {
		// lr/sc and the amos through a span element under the sequential
		// model (asm/rv64_atomics.go).
		return x.atomicRV64(kind, width, ops, state)
	}
	if width, isLoad := rv64Loads[name]; isLoad {
		mem := ops[1].(Memory)
		if mem.Base.Class != ClassSP {
			if base, bound := state.regs[mem.Base.Num]; bound {
				if global, isGlobal := globalAddrOf(base); isGlobal {
					return x.globalLoadRV64(reg(0), mem, width, name, global, state)
				}
			}
			return x.spanLoadRV64(reg(0), mem, width, name, state)
		}
		return x.frameAccessRV64(reg(0), mem, width, name, false, state)
	}
	if width, isStore := rv64Stores[name]; isStore {
		mem := ops[1].(Memory)
		if mem.Base.Class != ClassSP {
			if base, bound := state.regs[mem.Base.Num]; bound {
				if global, isGlobal := globalAddrOf(base); isGlobal {
					return x.globalStoreRV64(reg(0), mem, width, global, state)
				}
			}
			return x.spanStoreRV64(reg(0), mem, width, state)
		}
		return x.frameAccessRV64(reg(0), mem, width, name, true, state)
	}
	return "instruction " + instr.Mnemonic, false
}

// globalLoadRV64 reads a package global's cell: the value a store on this
// path put there, else the entry parameter `global:NAME`; lw/lh/lb
// sign-extend the cell into the register, lwu/lhu/lbu and ld leave it as
// the cell's width zero-extended (a Bool cell is one bit in its word).
func (x *pathExecutor) globalLoadRV64(dest Register, mem Memory, width int, name string, global string, state *symbolicState) (string, bool) {
	spec, known := x.globals[global]
	if !known {
		return "a load through the address of an undeclared global", false
	}
	if mem.Offset != 0 || width*8 != spec.Bits {
		return fmt.Sprintf("a %d-byte load at offset %d of the %d-bit global %s", width, mem.Offset, spec.Bits, global), false
	}
	value, written := state.globals[global]
	if !written {
		value = cellEntry(global, spec)
	}
	signExtending := name == "lw" || name == "lh" || name == "lb"
	if signExtending && cellWidth(spec) == spec.Bits {
		state.write(dest, extendTerm(value, spec.Bits, 64, true))
	} else {
		state.write(dest, zeroExtend(value, 64))
	}
	return "", true
}

// globalStoreRV64 writes a package global's cell at its width.
func (x *pathExecutor) globalStoreRV64(src Register, mem Memory, width int, global string, state *symbolicState) (string, bool) {
	spec, known := x.globals[global]
	if !known {
		return "a store through the address of an undeclared global", false
	}
	if mem.Offset != 0 || width*8 != spec.Bits {
		return fmt.Sprintf("a %d-byte store at offset %d to the %d-bit global %s", width, mem.Offset, spec.Bits, global), false
	}
	value, ok := state.read(src)
	if !ok {
		return "unbound register read", false
	}
	if state.globals == nil {
		state.globals = map[string]*term{}
	}
	state.globals[global] = truncate(value, cellWidth(spec))
	return "", true
}

// spanLoadRV64 resolves a load through a span base to the element it
// reads: the address is `&v + K` (a constant offset, K a multiple of the
// element size) or `&v + (idx << s)` with 2^s the element size — the
// checker's guarded-index idiom (docs/spec/94-assembler.md §9). The load
// width is the element width; lw/lh/lb sign-extend, lwu/lhu/lbu zero-extend.
func (x *pathExecutor) spanLoadRV64(dest Register, mem Memory, width int, name string, state *symbolicState) (string, bool) {
	if address, bound := state.regs[mem.Base.Num]; bound {
		if param, offset, isBase := spanBaseOf(address); isBase {
			if record, isRecord := x.records[param]; isRecord {
				// The caller's copy of a record argument: a load at a leaf's
				// exact offset and width is that leaf.
				value, ok := x.recordBytes(record.leaves, offset+mem.Offset, int64(width))
				if !ok {
					return "a load from a record argument cutting through a field", false
				}
				value = zeroExtend(value, 64)
				switch name {
				case "lw", "lh", "lb":
					value = extendTerm(value, width*8, 64, true)
				}
				state.write(dest, value)
				return "", true
			}
		}
	}
	span, index, reason, ok := x.rv64SpanAddress(mem, state)
	if !ok {
		return reason, false
	}
	if int64(width) != x.spans[span] {
		return fmt.Sprintf("a %d-byte load over %d-byte elements", width, x.spans[span]), false
	}
	element := x.elementIn(state, span, index, width*8)
	value := zeroExtend(element, 64)
	switch name {
	case "lw", "lh", "lb":
		value = extendTerm(value, width*8, 64, true)
	}
	state.write(dest, value)
	return "", true
}

// rv64SpanAddress resolves the address a load or store through a span
// base names: `&v + K` (a constant offset, K a multiple of the element
// size) or `&v + (idx << s)` with 2^s the element size — the checker's
// guarded-index idiom — as the span and the 32-bit element index.
func (x *pathExecutor) rv64SpanAddress(mem Memory, state *symbolicState) (span string, index *term, reason string, ok bool) {
	address, bound := state.regs[mem.Base.Num]
	if !bound {
		return "", nil, "a load through a register that is not a span base", false
	}
	if param, offset, isBase := spanBaseOf(address); isBase {
		elem := x.spans[param]
		offset += mem.Offset
		if elem == 0 || offset%elem != 0 || offset < 0 {
			return "", nil, "a span offset not aligned to an element", false
		}
		return param, constTerm(uint64(offset/elem), 32), "", true
	}
	if address.kind == termBinary && address.op == "add" {
		// &v + (idx << s), either order.
		base, scaled := address.left, address.right
		if _, _, isBase := spanBaseOf(base); !isBase {
			base, scaled = address.right, address.left
		}
		param, offset, isBase := spanBaseOf(base)
		if !isBase || offset != 0 || mem.Offset != 0 {
			return "", nil, "a load through an address that is not a span element", false
		}
		switch {
		case x.spans[param] == 1:
			// Byte elements: the index is the offset, unscaled.
			return param, truncate(scaled, 32), "", true
		case scaled.kind == termBinary && scaled.op == "shl" && scaled.right.kind == termConst && int64(1)<<scaled.right.value == x.spans[param]:
			return param, truncate(scaled.left, 32), "", true
		default:
			return "", nil, "an element address whose scale is not the element size", false
		}
	}
	return "", nil, "a load through a register that is not a span base", false
}

// spanStoreRV64 executes a store through a span parameter's base: the
// element at the address takes the stored register's value at the element
// width, in the path's write log (asm/effects.go), as the AArch64 lane's
// spanStore does; the Oak side's assignments are compared as memories.
func (x *pathExecutor) spanStoreRV64(src Register, mem Memory, width int, state *symbolicState) (string, bool) {
	if address, bound := state.regs[mem.Base.Num]; bound {
		if param, _, isBase := spanBaseOf(address); isBase {
			if _, isRecord := x.records[param]; isRecord {
				return "a store into a record argument", false
			}
		}
	}
	span, index, reason, ok := x.rv64SpanAddress(mem, state)
	if !ok {
		return strings.Replace(reason, "a load", "a store", 1), false
	}
	if int64(width) != x.spans[span] {
		return fmt.Sprintf("a %d-byte store over %d-byte elements", width, x.spans[span]), false
	}
	value, okValue := state.read(src)
	if !okValue {
		return "unbound register read", false
	}
	state.writes = appendWrite(state.writes, span, index, truncate(value, width*8), nil)
	return "", true
}

// frameAccessRV64 executes a load or store through the sp frame: the
// address is entry-relative (-disp + offset) as the checker computes it;
// a store records the value at its width, a load reads back the bytes it
// covers (whole slots or pieces of them) and extends them as the load
// spells.
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
		// A store splits the slots it overlaps and a load assembles the
		// bytes it covers from the slots holding them (storeSlot,
		// loadSlot), so a record chunk stored with sd is read back field
		// by field with lw or lbu, as the AArch64 lane's frame is.
		state.storeSlot(addr, truncate(value, 8*width), int64(width))
		return "", true
	}
	loaded, ok := x.loadFrame(state, addr, int64(width))
	if !ok {
		return "a load from a frame slot never stored on this path", false
	}
	value := zeroExtend(loaded, 64)
	switch name {
	case "lw", "lh", "lb":
		value = extendTerm(value, 8*width, 64, true)
	}
	state.write(reg, value)
	return "", true
}
