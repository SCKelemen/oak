package asm

import "strings"

// The RV64 lane's floating-point instructions as terms (docs/spec/
// 94-assembler.md §8 and §9): the F/D registers are a file of their own
// (symbolicState.fregs), each holding an IEEE bit pattern at the width of
// the instruction that wrote it. The arithmetic builds the same operation
// terms as the AArch64 lane and the Oak lowering (asm/floats_ops.go), so
// an f32/f64 unit is proven equal to its body up to the IEEE operations;
// the sign injections, the comparisons, and the bit moves are bit
// operations. RISC-V's fmin/fmax are IEEE minimumNumber/maximumNumber (a
// NaN operand suppressed), the `fminnm` terms — Oak's `min_num`/`max_num`,
// not its `min`/`max`.

// rv64FloatWidth is the width a mnemonic's suffix names (.s → 32, .d → 64).
func rv64FloatWidth(name string) (int, bool) {
	switch {
	case len(name) > 2 && name[len(name)-2:] == ".s":
		return 32, true
	case len(name) > 2 && name[len(name)-2:] == ".d":
		return 64, true
	}
	return 0, false
}

// rv64RoundingDynamic reports whether the optional rounding-mode operand
// is absent or `dyn`: the dynamic mode, round to nearest even under the
// contract (the harnesses and the C runtime never change fcsr.frm). A
// static mode other than rtz on a conversion is outside the model.
func rv64RoundingDynamic(ops []Operand, fixed int) (string, bool) {
	if len(ops) <= fixed {
		return "dyn", true
	}
	opt, isOpt := ops[fixed].(Option)
	if !isOpt {
		return "", false
	}
	return opt.Name, true
}

// stepRV64Float executes one instruction touching the floating-point file.
func (x *pathExecutor) stepRV64Float(instr Instruction, state *symbolicState) (string, bool) {
	ops := instr.Operands
	name := instr.Mnemonic
	reg := func(i int) Register { return ops[i].(Register) }
	read := func(i int) (*term, bool) { return state.read(reg(i)) }
	refuse := func(why string) (string, bool) { return "a floating-point instruction (" + name + ": " + why + ")", false }
	w, hasWidth := rv64FloatWidth(name)
	base := name
	if hasWidth && !strings.HasPrefix(name, "fcvt.") && !strings.HasPrefix(name, "fmv.") {
		base = name[:len(name)-2] // the arithmetic family: one case per operation, the suffix its width
	}
	switch base {
	case "fadd", "fsub", "fmul", "fdiv":
		rm, okRM := rv64RoundingDynamic(ops, 3)
		if !okRM || rm != "dyn" {
			return refuse("a static rounding mode")
		}
		a, okA := read(1)
		b, okB := read(2)
		if !okA || !okB {
			return "unbound floating-point register read", false
		}
		state.write(reg(0), floatTerm(base, w, truncate(a, w), truncate(b, w)))
		return "", true
	case "fsqrt":
		rm, okRM := rv64RoundingDynamic(ops, 2)
		if !okRM || rm != "dyn" {
			return refuse("a static rounding mode")
		}
		a, okA := read(1)
		if !okA {
			return "unbound floating-point register read", false
		}
		state.write(reg(0), floatTerm("fsqrt", w, truncate(a, w)))
		return "", true
	case "fmin", "fmax":
		a, okA := read(1)
		b, okB := read(2)
		if !okA || !okB {
			return "unbound floating-point register read", false
		}
		op := map[string]string{"fmin": "fminnm", "fmax": "fmaxnm"}[base]
		state.write(reg(0), floatTerm(op, w, truncate(a, w), truncate(b, w)))
		return "", true
	case "fsgnj", "fsgnjn", "fsgnjx":
		// rd takes rs1's magnitude and rs2's sign (negated; xored with
		// rs1's): fmv, fneg (rs1 = rs2), fabs (rs1 = rs2) are these.
		a, okA := read(1)
		b, okB := read(2)
		if !okA || !okB {
			return "unbound floating-point register read", false
		}
		a, b = truncate(a, w), truncate(b, w)
		sign, magnitude, _, _ := floatMasks(w)
		signBits := binaryTerm("and", b, constTerm(sign, w))
		switch base {
		case "fsgnjn":
			signBits = binaryTerm("xor", signBits, constTerm(sign, w))
		case "fsgnjx":
			signBits = binaryTerm("xor", signBits, binaryTerm("and", a, constTerm(sign, w)))
		}
		state.write(reg(0), binaryTerm("or", binaryTerm("and", a, constTerm(magnitude, w)), signBits))
		return "", true
	case "fmadd", "fmsub", "fnmadd", "fnmsub":
		// rd = rs1*rs2 + rs3; fmsub rs1*rs2 - rs3; fnmsub -(rs1*rs2) + rs3;
		// fnmadd -(rs1*rs2) - rs3 (RISC-V unprivileged spec §11.6), each one
		// rounding: fma over the sign-adjusted operands.
		rm, okRM := rv64RoundingDynamic(ops, 4)
		if !okRM || rm != "dyn" {
			return refuse("a static rounding mode")
		}
		a, okA := read(1)
		b, okB := read(2)
		c, okC := read(3)
		if !okA || !okB || !okC {
			return "unbound floating-point register read", false
		}
		a, b, c = truncate(a, w), truncate(b, w), truncate(c, w)
		switch base {
		case "fmsub":
			c = floatNeg(c, w)
		case "fnmsub":
			a = floatNeg(a, w)
		case "fnmadd":
			a, c = floatNeg(a, w), floatNeg(c, w)
		}
		state.write(reg(0), floatTerm("fma", w, a, b, c))
		return "", true
	case "feq", "flt", "fle":
		a, okA := read(1)
		b, okB := read(2)
		if !okA || !okB {
			return "unbound floating-point register read", false
		}
		op := map[string]string{"feq": "==", "flt": "<", "fle": "<="}[base]
		compared, _ := floatCompare(op, truncate(a, w), truncate(b, w), w)
		state.write(reg(0), zeroExtend(compared, 64))
		return "", true
	case "fmv.x.w", "fmv.x.d":
		a, okA := read(1)
		if !okA {
			return "unbound floating-point register read", false
		}
		if base == "fmv.x.w" {
			// The single's bits sign-extended to XLEN.
			state.write(reg(0), extendTerm(truncate(a, 32), 32, 64, true))
		} else {
			state.write(reg(0), truncate(a, 64))
		}
		return "", true
	case "fmv.w.x", "fmv.d.x":
		a, okA := read(1)
		if !okA {
			return "unbound register read", false
		}
		if base == "fmv.w.x" {
			state.write(reg(0), truncate(a, 32))
		} else {
			state.write(reg(0), a)
		}
		return "", true
	case "fcvt.s.d", "fcvt.d.s":
		a, okA := read(1)
		if !okA {
			return "unbound floating-point register read", false
		}
		if base == "fcvt.s.d" {
			state.write(reg(0), floatTerm("fcvt", 32, truncate(a, 64)))
		} else {
			state.write(reg(0), floatTerm("fcvt", 64, truncate(a, 32)))
		}
		return "", true
	case "fcvt.s.w", "fcvt.s.wu", "fcvt.s.l", "fcvt.s.lu", "fcvt.d.w", "fcvt.d.wu", "fcvt.d.l", "fcvt.d.lu":
		// An integer to a float: the source width and signedness are the
		// suffix's; the mode is dynamic (nearest even) — the exact ones
		// (fcvt.d.w, fcvt.d.wu) need none.
		rm, okRM := rv64RoundingDynamic(ops, 2)
		if !okRM || (rm != "dyn" && rm != "rne") {
			return refuse("a static rounding mode")
		}
		a, okA := read(1)
		if !okA {
			return "unbound register read", false
		}
		target := 32
		if base[5] == 'd' {
			target = 64
		}
		source := 32
		if base[7] == 'l' {
			source = 64
		}
		op := "scvtf"
		if base[len(base)-1] == 'u' {
			op = "ucvtf"
		}
		state.write(reg(0), floatTerm(op, target, truncate(a, source)))
		return "", true
	case "fcvt.w.s", "fcvt.wu.s", "fcvt.l.s", "fcvt.lu.s", "fcvt.w.d", "fcvt.wu.d", "fcvt.l.d", "fcvt.lu.d":
		// A float to an integer: the contract's conversion is toward zero
		// (saturating, NaN to zero), so the mode must be rtz; a 32-bit
		// result is sign-extended to XLEN.
		rm, okRM := rv64RoundingDynamic(ops, 2)
		if !okRM || rm != "rtz" {
			return refuse("a float-to-integer conversion without rtz (the contract converts toward zero)")
		}
		a, okA := read(1)
		if !okA {
			return "unbound floating-point register read", false
		}
		source := 32
		if base[len(base)-1] == 'd' {
			source = 64
		}
		target := 32
		if base[5] == 'l' {
			target = 64
		}
		op := "fcvtzs"
		if base[6] == 'u' {
			op = "fcvtzu"
		}
		value := floatTerm(op, target, truncate(a, source))
		if target == 32 {
			value = extendTerm(value, 32, 64, true)
		} else {
			value = zeroExtend(value, 64)
		}
		state.write(reg(0), value)
		return "", true
	}
	if width, isLoad := rv64FloatLoads[name]; isLoad {
		mem, isMem := ops[1].(Memory)
		if !isMem || mem.Base.Class != ClassSP {
			return refuse("floating-point memory is frame memory")
		}
		return x.frameAccessRV64Float(reg(0), mem, width, false, state)
	}
	if width, isStore := rv64FloatStores[name]; isStore {
		mem, isMem := ops[1].(Memory)
		if !isMem || mem.Base.Class != ClassSP {
			return refuse("floating-point memory is frame memory")
		}
		return x.frameAccessRV64Float(reg(0), mem, width, true, state)
	}
	return refuse("outside the modeled subset")
}

// frameAccessRV64Float is flw/fld/fsw/fsd through the sp frame: a slot at
// the access width, read back at the same width (no extension: the pattern
// is the value).
func (x *pathExecutor) frameAccessRV64Float(reg Register, mem Memory, width int, store bool, state *symbolicState) (string, bool) {
	addr := -state.disp + mem.Offset
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	if store {
		value, ok := state.read(reg)
		if !ok {
			return "unbound floating-point register read", false
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
	state.write(reg, truncate(slot.value, 8*width))
	return "", true
}
