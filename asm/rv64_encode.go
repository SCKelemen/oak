package asm

import "fmt"

// The RV64 encoder (docs/spec/94-assembler.md §9): every base instruction
// is one 32-bit word whose fixed bits come from the generated table
// (asm/rv64_encodings_gen.go, from riscv-opcodes) and whose argument
// fields are placed here by name. The immediates are the ISA's permuted
// forms: jimm20 is [20|10:1|11|19:12], the branch pair bimm12hi/lo is
// [12|10:5] and [4:1|11], the store pair imm12hi/lo is [11:5] and [4:0].
// Labels resolve within the function; `call sym` (auipc ra + jalr ra)
// leaves an R_RISCV_CALL_PLT relocation on its first word.

// rv64ExactConversions are the conversions whose result is always exact
// (a 32-bit integer or a single fits a double): the rounding-mode field is
// meaningless and GNU as encodes rne (0) unless a mode is spelled.
var rv64ExactConversions = map[string]bool{"fcvt.d.w": true, "fcvt.d.wu": true, "fcvt.d.s": true}

// rv64Words is the number of 32-bit words an instruction spends: one,
// except a 32-bit `li` (lui, then addiw unless the low part is zero).
func rv64Words(instr Instruction) int {
	if instr.Mnemonic == "call" {
		return 2
	}
	if instr.Mnemonic == "li" {
		value := instr.Operands[1].(Immediate).Value
		if value >= -2048 && value <= 2047 {
			return 1
		}
		if _, lo := rv64SplitImmediate(value); lo == 0 {
			return 1
		}
		return 2
	}
	return 1
}

// rv64SplitImmediate splits a 32-bit value into the lui part and the
// signed 12-bit addiw part: value = (hi << 12) + lo with lo in [-2048, 2047].
func rv64SplitImmediate(value int64) (hi, lo int64) {
	hi = (value + 0x800) >> 12
	lo = value - (hi << 12)
	return hi, lo
}

func encodeRV64Function(fn *Function) ([]byte, []Relocation, error) {
	labels := map[string]int64{}
	offset := int64(0)
	for _, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			labels[it.Name] = offset
		case Instruction:
			offset += 4 * int64(rv64Words(it))
		case Align:
			return nil, nil, fmt.Errorf("%s:%d: align regions are not admitted for rv64 units", fn.Name, it.Line)
		}
	}
	var out []byte
	var relocs []Relocation
	offset = 0
	emit := func(word uint32) {
		out = append(out, byte(word), byte(word>>8), byte(word>>16), byte(word>>24))
		offset += 4
	}
	for _, item := range fn.Items {
		instr, isInstr := item.(Instruction)
		if !isInstr {
			continue
		}
		if instr.Mnemonic == "li" {
			value := instr.Operands[1].(Immediate).Value
			if value < -(1<<31) || value >= 1<<31 {
				return nil, nil, fmt.Errorf("%s:%d: li admits 32-bit immediates in this increment (%d)", fn.Name, instr.Line, value)
			}
			if value < -2048 || value > 2047 {
				hi, lo := rv64SplitImmediate(value)
				rd := instr.Operands[0].(Register)
				word, err := encodeRV64Instruction(Instruction{Mnemonic: "lui", Operands: []Operand{rd, Immediate{Value: hi}}}, offset, labels)
				if err != nil {
					return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, instr.Line, err)
				}
				emit(word)
				if lo != 0 {
					word, err = encodeRV64Instruction(Instruction{Mnemonic: "addiw", Operands: []Operand{rd, rd, Immediate{Value: lo}}}, offset, labels)
					if err != nil {
						return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, instr.Line, err)
					}
					emit(word)
				}
				continue
			}
		}
		if instr.Mnemonic == "call" {
			// auipc ra, 0; jalr ra, 0(ra) — the linker fills both under one
			// R_RISCV_CALL_PLT at the auipc.
			ra := Register{Text: "ra", Class: ClassRV64X, Num: 1, Lane: -1}
			relocs = append(relocs, Relocation{Offset: int(offset), Kind: "riscv_call_plt", Symbol: instr.Operands[0].(Symbol).Name})
			word, err := encodeRV64Instruction(Instruction{Mnemonic: "auipc", Operands: []Operand{ra, Immediate{Value: 0}}}, offset, labels)
			if err != nil {
				return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, instr.Line, err)
			}
			emit(word)
			word, err = encodeRV64Instruction(Instruction{Mnemonic: "jalr", Operands: []Operand{ra, Memory{Base: ra, Mode: MemOffset}}}, offset, labels)
			if err != nil {
				return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, instr.Line, err)
			}
			emit(word)
			continue
		}
		base := rv64Base(instr)
		word, err := encodeRV64Instruction(base, offset, labels)
		if err != nil {
			return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, instr.Line, err)
		}
		emit(word)
	}
	return out, relocs, nil
}

// encodeRV64Instruction encodes one base instruction at byte offset pc.
func encodeRV64Instruction(instr Instruction, pc int64, labels map[string]int64) (uint32, error) {
	enc, known := rv64Table[instr.Mnemonic]
	if !known {
		return 0, fmt.Errorf("no encoding for %s", instr.Mnemonic)
	}
	ops := instr.Operands
	fields := map[string]int64{}
	regNum := func(i int) int64 { return int64(rv64Number(ops[i].(Register))) }
	branchOffset := func(sym Symbol, bits int) (int64, error) {
		target, isLabel := labels[sym.Name]
		if !isLabel {
			return 0, fmt.Errorf("%s reaches only labels within the function (%s)", instr.Mnemonic, sym.Name)
		}
		delta := target - pc
		limit := int64(1) << uint(bits-1)
		if delta%2 != 0 || delta < -limit || delta >= limit {
			return 0, fmt.Errorf("branch to %s is out of range (%d bytes)", sym.Name, delta)
		}
		return delta, nil
	}
	switch {
	case rv64FloatShapes[instr.Mnemonic] != "":
		// rd, rs1, rs2, rs3 by position; the rounding mode (rm) from the
		// trailing option, dyn (0b111) when absent — GNU as's default.
		names := []string{"rd", "rs1", "rs2", "rs3"}
		fields["rm"] = 7
		if rv64ExactConversions[instr.Mnemonic] {
			// An exact conversion never rounds; the assemblers encode rne.
			fields["rm"] = 0
		}
		for i, operand := range ops {
			switch o := operand.(type) {
			case Register:
				if i < len(names) {
					fields[names[i]] = int64(rv64Number(o))
				}
			case Option:
				fields["rm"] = rv64RoundingModes[o.Name]
			}
		}
	case rv64FloatLoads[instr.Mnemonic] != 0:
		mem := ops[1].(Memory)
		fields["rd"], fields["rs1"], fields["imm12"] = regNum(0), int64(rv64Number(mem.Base)), mem.Offset
	case rv64FloatStores[instr.Mnemonic] != 0:
		mem := ops[1].(Memory)
		if mem.Offset < -2048 || mem.Offset > 2047 {
			return 0, fmt.Errorf("store offset %d is outside the 12-bit signed range", mem.Offset)
		}
		fields["rs2"], fields["rs1"] = regNum(0), int64(rv64Number(mem.Base))
		fields["imm12hi"], fields["imm12lo"] = mem.Offset>>5&0x7f, mem.Offset&0x1f
	case rv64Branches[instr.Mnemonic]:
		delta, err := branchOffset(ops[2].(Symbol), 13)
		if err != nil {
			return 0, err
		}
		fields["rs1"], fields["rs2"] = regNum(0), regNum(1)
		fields["bimm12hi"] = (delta>>12&1)<<6 | (delta >> 5 & 0x3f)
		fields["bimm12lo"] = (delta>>1&0xf)<<1 | (delta >> 11 & 1)
	case instr.Mnemonic == "jal":
		delta, err := branchOffset(ops[1].(Symbol), 21)
		if err != nil {
			return 0, err
		}
		fields["rd"] = regNum(0)
		fields["jimm20"] = (delta>>20&1)<<19 | (delta>>1&0x3ff)<<9 | (delta>>11&1)<<8 | (delta >> 12 & 0xff)
	case instr.Mnemonic == "jalr":
		mem := ops[1].(Memory)
		fields["rd"], fields["rs1"], fields["imm12"] = regNum(0), int64(rv64Number(mem.Base)), mem.Offset
	case instr.Mnemonic == "lui" || instr.Mnemonic == "auipc":
		imm := ops[1].(Immediate).Value
		if imm < -(1<<19) || imm > (1<<20)-1 {
			return 0, fmt.Errorf("%s immediate %d is outside the 20-bit range", instr.Mnemonic, imm)
		}
		fields["rd"], fields["imm20"] = regNum(0), imm&0xfffff
	case rv64Loads[instr.Mnemonic] != 0:
		mem := ops[1].(Memory)
		fields["rd"], fields["rs1"], fields["imm12"] = regNum(0), int64(rv64Number(mem.Base)), mem.Offset
	case rv64Stores[instr.Mnemonic] != 0:
		mem := ops[1].(Memory)
		if mem.Offset < -2048 || mem.Offset > 2047 {
			return 0, fmt.Errorf("store offset %d is outside the 12-bit signed range", mem.Offset)
		}
		fields["rs2"], fields["rs1"] = regNum(0), int64(rv64Number(mem.Base))
		fields["imm12hi"], fields["imm12lo"] = mem.Offset>>5&0x7f, mem.Offset&0x1f
	case len(ops) == 3:
		fields["rd"], fields["rs1"] = regNum(0), regNum(1)
		switch third := ops[2].(type) {
		case Register:
			fields["rs2"] = int64(rv64Number(third))
		case Immediate:
			fields["imm12"], fields["shamtd"], fields["shamtw"] = third.Value, third.Value, third.Value
		}
	default:
		return 0, fmt.Errorf("operand shape of %s", instr.Mnemonic)
	}
	word := enc.Value
	for _, arg := range enc.Args {
		value, present := fields[arg.Name]
		if !present {
			return 0, fmt.Errorf("%s: no operand for field %s", instr.Mnemonic, arg.Name)
		}
		width := uint(arg.Hi - arg.Lo + 1)
		switch arg.Name {
		case "imm12":
			if value < -2048 || value > 2047 {
				return 0, fmt.Errorf("%s immediate %d is outside the 12-bit signed range", instr.Mnemonic, value)
			}
		case "shamtd":
			if value < 0 || value > 63 {
				return 0, fmt.Errorf("shift amount %d is outside 0..63", value)
			}
		case "shamtw":
			if value < 0 || value > 31 {
				return 0, fmt.Errorf("shift amount %d is outside 0..31", value)
			}
		}
		word |= uint32(uint64(value)&((uint64(1)<<width)-1)) << uint(arg.Lo)
	}
	if word&enc.Mask != enc.Value {
		return 0, fmt.Errorf("%s: an operand field overlaps the fixed bits", instr.Mnemonic)
	}
	return word, nil
}
