package asm

// RVC, the compressed encodings of the RV64 lane (docs/spec/94-assembler.md
// §9, RISC-V ISA volume I chapter "C" extension). Every compressed
// instruction is one base instruction of the lane with operands that fit a
// 16-bit form — a register from the compressed set x8–x15 where the form
// names three bits, a 6-bit signed immediate, a scaled and bounded offset —
// so the checker and the verifier see the base instruction and only the
// encoder chooses. The choice follows GNU as: compress whenever a form
// exists and the operands fit; branches and jumps compress once their
// offsets fit (the layout converges from four-byte instructions by
// shrinking). The fields are the generated table's (rv_c, rv64_c), the
// immediates scattered as the ISA lays them out.

// rvcReg reports a register of the compressed set x8–x15 and its 3-bit index.
func rvcReg(reg Register) (int64, bool) {
	n := int64(rv64Number(reg))
	return n - 8, n >= 8 && n <= 15
}

func rvcNum(reg Register) int64 { return int64(rv64Number(reg)) }

func fits6(v int64) bool { return v >= -32 && v <= 31 }

// rvcBits extracts value[hi:lo].
func rvcBits(value int64, hi, lo uint) int64 { return (value >> lo) & ((1 << (hi - lo + 1)) - 1) }

// rvcCompressible reports whether a base instruction has a compressed form
// for its register and immediate operands; branch and jump offsets are
// decided by rvcEncode with the layout.
func rvcCompressible(base Instruction) bool {
	name, _, ok := rvcForm(base, 0, nil, false)
	return ok && name != ""
}

// rvcEncode encodes the compressed form of a base instruction at pc, or
// reports that none fits (a branch out of the compressed range included).
func rvcEncode(base Instruction, pc int64, labels map[string]int64) (uint16, bool) {
	name, fields, ok := rvcForm(base, pc, labels, true)
	if !ok {
		return 0, false
	}
	enc, known := rv64Table[name]
	if !known {
		return 0, false
	}
	word := enc.Value
	for _, arg := range enc.Args {
		value, present := fields[arg.Name]
		if !present {
			return 0, false
		}
		width := uint(arg.Hi - arg.Lo + 1)
		word |= uint32(uint64(value)&((uint64(1)<<width)-1)) << uint(arg.Lo)
	}
	return uint16(word), true
}

// rvcForm names the compressed mnemonic and its fields. With offsets false
// a branch or jump is admitted by shape alone (the layout decides its
// size later); with offsets true its label offset must fit.
func rvcForm(base Instruction, pc int64, labels map[string]int64, offsets bool) (string, map[string]int64, bool) {
	ops := base.Operands
	f := map[string]int64{}
	reg := func(i int) Register { return ops[i].(Register) }
	imm6 := func(v int64, hi, lo string) { f[hi] = rvcBits(v, 5, 5); f[lo] = rvcBits(v, 4, 0) }
	branchOffset := func(sym Symbol) (int64, bool) {
		target, isLabel := labels[sym.Name]
		if !isLabel {
			return 0, false
		}
		return target - pc, true
	}
	switch base.Mnemonic {
	case "addi":
		rd, rs1, imm := reg(0), reg(1), ops[2].(Immediate).Value
		d, s := rvcNum(rd), rvcNum(rs1)
		switch {
		case d == 0 && s == 0 && imm == 0:
			f["c_nzimm6hi"], f["c_nzimm6lo"] = 0, 0
			return "c.nop", f, true
		case s == 0 && d != 0 && fits6(imm):
			f["rd_n0"] = d
			imm6(imm, "c_imm6hi", "c_imm6lo")
			return "c.li", f, true
		case d == s && d != 0 && imm != 0 && fits6(imm):
			// GNU as takes c.addi before c.addi16sp when the immediate fits.
			f["rd_rs1_n0"] = d
			imm6(imm, "c_nzimm6hi", "c_nzimm6lo")
			return "c.addi", f, true
		case d == 2 && s == 2 && imm != 0 && imm%16 == 0 && imm >= -512 && imm <= 496:
			f["c_nzimm10hi"] = rvcBits(imm, 9, 9)
			f["c_nzimm10lo"] = rvcBits(imm, 4, 4)<<4 | rvcBits(imm, 6, 6)<<3 | rvcBits(imm, 8, 7)<<1 | rvcBits(imm, 5, 5)
			return "c.addi16sp", f, true
		case s == 2 && d >= 8 && d <= 15 && imm > 0 && imm%4 == 0 && imm < 1024:
			f["rd_p"] = d - 8
			f["c_nzuimm10"] = rvcBits(imm, 5, 4)<<6 | rvcBits(imm, 9, 6)<<2 | rvcBits(imm, 2, 2)<<1 | rvcBits(imm, 3, 3)
			return "c.addi4spn", f, true
		case imm == 0 && d != 0 && s != 0 && d != s:
			f["rd_n0"], f["c_rs2_n0"] = d, s
			return "c.mv", f, true
		}
	case "addiw":
		rd, rs1, imm := reg(0), reg(1), ops[2].(Immediate).Value
		if rvcNum(rd) == rvcNum(rs1) && rvcNum(rd) != 0 && fits6(imm) {
			f["rd_rs1_n0"] = rvcNum(rd)
			imm6(imm, "c_imm6hi", "c_imm6lo")
			return "c.addiw", f, true
		}
	case "lui":
		rd, imm := reg(0), ops[1].(Immediate).Value
		if rvcNum(rd) != 0 && rvcNum(rd) != 2 && imm != 0 && fits6(imm) {
			f["rd_n2"] = rvcNum(rd)
			imm6(imm, "c_nzimm18hi", "c_nzimm18lo")
			return "c.lui", f, true
		}
	case "slli":
		rd, rs1, sh := reg(0), reg(1), ops[2].(Immediate).Value
		if rvcNum(rd) == rvcNum(rs1) && rvcNum(rd) != 0 && sh >= 1 && sh <= 63 {
			f["rd_rs1_n0"] = rvcNum(rd)
			imm6(sh, "c_nzuimm6hi", "c_nzuimm6lo")
			return "c.slli", f, true
		}
	case "srli", "srai":
		rd, rs1, sh := reg(0), reg(1), ops[2].(Immediate).Value
		if p, in := rvcReg(rd); in && rvcNum(rd) == rvcNum(rs1) && sh >= 1 && sh <= 63 {
			f["rd_rs1_p"] = p
			imm6(sh, "c_nzuimm6hi", "c_nzuimm6lo")
			return "c." + base.Mnemonic, f, true
		}
	case "andi":
		rd, rs1, imm := reg(0), reg(1), ops[2].(Immediate).Value
		if p, in := rvcReg(rd); in && rvcNum(rd) == rvcNum(rs1) && fits6(imm) {
			f["rd_rs1_p"] = p
			imm6(imm, "c_imm6hi", "c_imm6lo")
			return "c.andi", f, true
		}
	case "add":
		rd, rs1, rs2 := reg(0), reg(1), reg(2)
		d := rvcNum(rd)
		if d != 0 {
			// c.add rd, rs: rd is one source; the other is any register but x0.
			if rvcNum(rs1) == d && rvcNum(rs2) != 0 {
				f["rd_rs1_n0"], f["c_rs2_n0"] = d, rvcNum(rs2)
				return "c.add", f, true
			}
			if rvcNum(rs2) == d && rvcNum(rs1) != 0 {
				f["rd_rs1_n0"], f["c_rs2_n0"] = d, rvcNum(rs1)
				return "c.add", f, true
			}
		}
	case "sub", "xor", "or", "and", "subw", "addw":
		rd, rs1, rs2 := reg(0), reg(1), reg(2)
		p, in := rvcReg(rd)
		if !in {
			break
		}
		commutative := base.Mnemonic != "sub" && base.Mnemonic != "subw"
		other := rs2
		if rvcNum(rs1) != rvcNum(rd) {
			if !commutative || rvcNum(rs2) != rvcNum(rd) {
				break
			}
			other = rs1
		}
		if q, in := rvcReg(other); in {
			f["rd_rs1_p"], f["rs2_p"] = p, q
			return "c." + base.Mnemonic, f, true
		}
	case "lw", "ld":
		rd, mem := reg(0), ops[1].(Memory)
		scale := int64(4)
		if base.Mnemonic == "ld" {
			scale = 8
		}
		if mem.Offset < 0 || mem.Offset%scale != 0 {
			break
		}
		if mem.Base.Class == ClassSP {
			if rvcNum(rd) == 0 || mem.Offset >= 64*scale {
				break
			}
			f["rd_n0"] = rvcNum(rd)
			if scale == 4 {
				f["c_uimm8sphi"], f["c_uimm8splo"] = rvcBits(mem.Offset, 5, 5), rvcBits(mem.Offset, 4, 2)<<2|rvcBits(mem.Offset, 7, 6)
				return "c.lwsp", f, true
			}
			f["c_uimm9sphi"], f["c_uimm9splo"] = rvcBits(mem.Offset, 5, 5), rvcBits(mem.Offset, 4, 3)<<3|rvcBits(mem.Offset, 8, 6)
			return "c.ldsp", f, true
		}
		p, inD := rvcReg(rd)
		q, inB := rvcReg(mem.Base)
		if !inD || !inB || mem.Offset >= 32*scale {
			break
		}
		f["rd_p"], f["rs1_p"] = p, q
		if scale == 4 {
			f["c_uimm7hi"], f["c_uimm7lo"] = rvcBits(mem.Offset, 5, 3), rvcBits(mem.Offset, 2, 2)<<1|rvcBits(mem.Offset, 6, 6)
			return "c.lw", f, true
		}
		f["c_uimm8hi"], f["c_uimm8lo"] = rvcBits(mem.Offset, 5, 3), rvcBits(mem.Offset, 7, 6)
		return "c.ld", f, true
	case "sw", "sd":
		rs2, mem := reg(0), ops[1].(Memory)
		scale := int64(4)
		if base.Mnemonic == "sd" {
			scale = 8
		}
		if mem.Offset < 0 || mem.Offset%scale != 0 {
			break
		}
		if mem.Base.Class == ClassSP {
			if mem.Offset >= 64*scale {
				break
			}
			f["c_rs2"] = rvcNum(rs2)
			if scale == 4 {
				f["c_uimm8sp_s"] = rvcBits(mem.Offset, 5, 2)<<2 | rvcBits(mem.Offset, 7, 6)
				return "c.swsp", f, true
			}
			f["c_uimm9sp_s"] = rvcBits(mem.Offset, 5, 3)<<3 | rvcBits(mem.Offset, 8, 6)
			return "c.sdsp", f, true
		}
		p, inS := rvcReg(rs2)
		q, inB := rvcReg(mem.Base)
		if !inS || !inB || mem.Offset >= 32*scale {
			break
		}
		f["rs2_p"], f["rs1_p"] = p, q
		if scale == 4 {
			f["c_uimm7hi"], f["c_uimm7lo"] = rvcBits(mem.Offset, 5, 3), rvcBits(mem.Offset, 2, 2)<<1|rvcBits(mem.Offset, 6, 6)
			return "c.sw", f, true
		}
		f["c_uimm8hi"], f["c_uimm8lo"] = rvcBits(mem.Offset, 5, 3), rvcBits(mem.Offset, 7, 6)
		return "c.sd", f, true
	case "beq", "bne":
		rs1, rs2 := reg(0), reg(1)
		// beqz/bnez: the compared register in the compressed set against
		// x0 in the second position (GNU as does not swap the operands).
		if rvcNum(rs2) != 0 {
			break
		}
		p, in := rvcReg(rs1)
		if !in {
			break
		}
		f["rs1_p"] = p
		if !offsets {
			return "c.b" + base.Mnemonic[1:] + "z", f, true
		}
		delta, ok := branchOffset(ops[2].(Symbol))
		if !ok || delta%2 != 0 || delta < -256 || delta > 254 {
			break
		}
		f["c_bimm9hi"] = rvcBits(delta, 8, 8)<<2 | rvcBits(delta, 4, 3)
		f["c_bimm9lo"] = rvcBits(delta, 7, 6)<<3 | rvcBits(delta, 2, 1)<<1 | rvcBits(delta, 5, 5)
		return "c.b" + base.Mnemonic[1:] + "z", f, true
	case "jal":
		if rvcNum(reg(0)) != 0 {
			break // RV64 has no c.jal
		}
		if !offsets {
			return "c.j", f, true
		}
		delta, ok := branchOffset(ops[1].(Symbol))
		if !ok || delta%2 != 0 || delta < -2048 || delta > 2046 {
			break
		}
		f["c_imm12"] = rvcBits(delta, 11, 11)<<10 | rvcBits(delta, 4, 4)<<9 | rvcBits(delta, 9, 8)<<7 | rvcBits(delta, 10, 10)<<6 |
			rvcBits(delta, 6, 6)<<5 | rvcBits(delta, 7, 7)<<4 | rvcBits(delta, 3, 1)<<1 | rvcBits(delta, 5, 5)
		return "c.j", f, true
	case "jalr":
		rd, mem := reg(0), ops[1].(Memory)
		if mem.Offset != 0 {
			break
		}
		base1 := rvcNum(mem.Base)
		if base1 == 0 {
			break
		}
		switch rvcNum(rd) {
		case 0:
			f["rs1_n0"] = base1
			return "c.jr", f, true
		case 1:
			f["c_rs1_n0"] = base1
			return "c.jalr", f, true
		}
	case "ebreak":
		return "c.ebreak", f, true
	}
	return "", nil, false
}
