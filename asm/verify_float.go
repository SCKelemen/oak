package asm

import "math"

// The AArch64 floating-point instructions as terms (docs/spec/94-assembler.md
// §8, "floating point as uninterpreted operations"): a scalar view sN/dN of
// a vector register is the low lane of the register at its width, and the
// float arrangements 2s/4s/2d are lanes like the integer ones. The
// arithmetic instructions build the operation terms of asm/floats_ops.go —
// the same constructors the Oak lowering applies to `a + b`, `fma(...)`,
// `sqrt(...)`, and the simd float operations — so a unit is proven equal
// to its body up to the IEEE operations. The sign operations, the
// comparisons, and the selects are bit operations, as on the Oak side
// (asm/floats_lowering.go).

// scalarFloatWidth is the width of a scalar float view (sN → 32, dN → 64).
func scalarFloatWidth(reg Register) (int, bool) {
	if reg.Class != ClassV || reg.Lane >= 0 {
		return 0, false
	}
	switch reg.Vec {
	case "s":
		return 32, true
	case "d":
		return 64, true
	}
	return 0, false
}

// floatArrangement is a float arrangement's lane count and width.
func floatArrangement(arr string) (count, bits int, ok bool) {
	switch arr {
	case "2s":
		return 2, 32, true
	case "4s":
		return 4, 32, true
	case "2d":
		return 2, 64, true
	}
	return 0, 0, false
}

// floatNeg and floatAbs are the sign operations over a w-bit pattern.
func floatNeg(t *term, w int) *term { return binaryTerm("xor", t, constTerm(uint64(1)<<uint(w-1), w)) }
func floatAbs(t *term, w int) *term {
	_, magnitude, _, _ := floatMasks(w)
	return binaryTerm("and", t, constTerm(magnitude, w))
}

// floatArith is a lane of the arithmetic instructions: the operation
// term, or the bit operation for the sign and the min/max forms.
func floatArith(mnemonic string, w int, args ...*term) (*term, bool) {
	switch mnemonic {
	case "fadd", "fsub", "fmul", "fdiv":
		return floatTerm(mnemonic, w, args[0], args[1]), true
	case "fminnm":
		return floatMinMaxNum("min", args[0], args[1], w), true
	case "fmaxnm":
		return floatMinMaxNum("max", args[0], args[1], w), true
	case "fmin":
		return floatMinMax("min", args[0], args[1], w), true
	case "fmax":
		return floatMinMax("max", args[0], args[1], w), true
	case "fsqrt":
		return floatTerm("fsqrt", w, args[0]), true
	case "fneg":
		return floatNeg(args[0], w), true
	case "fabs":
		return floatAbs(args[0], w), true
	}
	return nil, false
}

// floatCondition reads a condition code off the flags fcmp left, right
// left: N is less, Z is equal, C is not less (greater, equal, or
// unordered), V is unordered (Arm ARM C6.2.61, FCMP). Each code is the
// IEEE predicate the compilers use it for.
func floatCondition(code string, left, right *term, w int) (*term, bool) {
	cmp := func(op string) *term {
		t, _ := floatCompare(op, left, right, w)
		return t
	}
	unordered := orBit(floatIsNaN(left, w), floatIsNaN(right, w))
	switch code {
	case "eq":
		return cmp("=="), true
	case "ne":
		return cmp("!="), true
	case "mi", "lo", "cc":
		return cmp("<"), true
	case "ls":
		return cmp("<="), true
	case "gt":
		return cmp(">"), true
	case "ge":
		return cmp(">="), true
	case "pl":
		return notBit(cmp("<")), true
	case "hi":
		return orBit(cmp(">"), unordered), true
	case "lt":
		return orBit(cmp("<"), unordered), true
	case "le":
		return orBit(cmp("<="), unordered), true
	case "hs", "cs":
		return orBit(cmp(">="), unordered), true
	case "vs":
		return unordered, true
	case "vc":
		return notBit(unordered), true
	}
	return nil, false
}

// stepFloat executes a floating-point instruction over scalar views or
// float arrangements. handled is false for an instruction this file does
// not model (the vector executor's integer cases follow).
func (x *pathExecutor) stepFloat(instr Instruction, state *symbolicState) (handled bool, reason string, ok bool) {
	ops := instr.Operands
	reg := func(i int) (Register, bool) {
		if i >= len(ops) {
			return Register{}, false
		}
		r, isReg := ops[i].(Register)
		return r, isReg
	}
	readScalar := func(r Register) (*term, bool) { return state.readVecView(r) }
	writeScalar := func(r Register, t *term) { state.writeVec(r.Num, vecFromLow(zeroExtend(t, 64))) }
	d, okD := reg(0)
	if !okD {
		return false, "", true
	}
	// Scalar forms: every register operand a view of one width.
	if w, isScalar := scalarFloatWidth(d); isScalar {
		switch instr.Mnemonic {
		case "fadd", "fsub", "fmul", "fdiv", "fmin", "fmax", "fminnm", "fmaxnm":
			n, okN := reg(1)
			m, okM := reg(2)
			if wn, isN := scalarFloatWidth(n); !okN || !okM || !isN || wn != w {
				return true, "a floating-point instruction over mixed views (" + instr.Mnemonic + ")", false
			}
			if wm, isM := scalarFloatWidth(m); !isM || wm != w {
				return true, "a floating-point instruction over mixed views (" + instr.Mnemonic + ")", false
			}
			a, okA := readScalar(n)
			b, okB := readScalar(m)
			if !okA || !okB {
				return true, "unbound vector register read", false
			}
			value, _ := floatArith(instr.Mnemonic, w, a, b)
			writeScalar(d, value)
			return true, "", true
		case "fsqrt", "fneg", "fabs", "fmov":
			n, okN := reg(1)
			if !okN {
				if imm, isFloat := ops[1].(FloatImmediate); isFloat && instr.Mnemonic == "fmov" {
					value, _ := floatLiteralBits(imm.Value, w)
					writeScalar(d, value)
					return true, "", true
				}
				return true, "a floating-point instruction without a register source (" + instr.Mnemonic + ")", false
			}
			if wn, isN := scalarFloatWidth(n); !isN || wn != w {
				if instr.Mnemonic == "fmov" {
					return false, "", true // fmov between the files: the vector executor's case
				}
				return true, "a floating-point instruction over mixed views (" + instr.Mnemonic + ")", false
			}
			a, okA := readScalar(n)
			if !okA {
				return true, "unbound vector register read", false
			}
			if instr.Mnemonic == "fmov" {
				writeScalar(d, a)
				return true, "", true
			}
			value, _ := floatArith(instr.Mnemonic, w, a)
			writeScalar(d, value)
			return true, "", true
		case "fmadd", "fmsub", "fnmadd", "fnmsub":
			// d = a + n*m; fmsub d = a - n*m; fnmadd d = -a - n*m; fnmsub d = -a + n*m;
			// each one rounding: fma over the sign-adjusted operands.
			n, okN := reg(1)
			m, okM := reg(2)
			a, okA := reg(3)
			if !okN || !okM || !okA {
				return true, "a fused multiply-add without three sources", false
			}
			for _, r := range []Register{n, m, a} {
				if wr, isR := scalarFloatWidth(r); !isR || wr != w {
					return true, "a floating-point instruction over mixed views (" + instr.Mnemonic + ")", false
				}
			}
			tn, okTN := readScalar(n)
			tm, okTM := readScalar(m)
			ta, okTA := readScalar(a)
			if !okTN || !okTM || !okTA {
				return true, "unbound vector register read", false
			}
			switch instr.Mnemonic {
			case "fmsub":
				tn = floatNeg(tn, w)
			case "fnmadd":
				tn, ta = floatNeg(tn, w), floatNeg(ta, w)
			case "fnmsub":
				ta = floatNeg(ta, w)
			}
			writeScalar(d, floatTerm("fma", w, tn, tm, ta))
			return true, "", true
		case "fcvt":
			n, okN := reg(1)
			wn, isN := scalarFloatWidth(n)
			if !okN || !isN || wn == w {
				return true, "fcvt between views of one width", false
			}
			a, okA := readScalar(n)
			if !okA {
				return true, "unbound vector register read", false
			}
			writeScalar(d, floatTerm("fcvt", w, a))
			return true, "", true
		case "scvtf", "ucvtf":
			n, okN := reg(1)
			if !okN || (n.Class != ClassW && n.Class != ClassX) {
				return true, instr.Mnemonic + " from a source that is not an integer register", false
			}
			value, okV := state.read(n)
			if !okV {
				return true, "unbound register read", false
			}
			writeScalar(d, floatTerm(instr.Mnemonic, w, truncate(value, widthOf(n.Class))))
			return true, "", true
		case "fcsel":
			n, okN := reg(1)
			m, okM := reg(2)
			if !okN || !okM || len(ops) != 4 {
				return true, "fcsel without two sources and a condition", false
			}
			cond, isCond := ops[3].(Condition)
			if !isCond {
				return true, "fcsel without a condition", false
			}
			if state.flags == nil || state.flags.unknown {
				return true, "fcsel reading flags no compare produced", false
			}
			a, okA := readScalar(n)
			b, okB := readScalar(m)
			if !okA || !okB {
				return true, "unbound vector register read", false
			}
			writeScalar(d, iteTerm(flagsCondition(cond.Code, state.flags), a, b))
			return true, "", true
		case "fcmp", "fcmpe":
			a, okA := readScalar(d)
			if !okA {
				return true, "unbound vector register read", false
			}
			var b *term
			if n, okN := reg(1); okN {
				if wn, isN := scalarFloatWidth(n); !isN || wn != w {
					return true, "fcmp over mixed views", false
				}
				var okB bool
				if b, okB = readScalar(n); !okB {
					return true, "unbound vector register read", false
				}
			} else if imm, isFloat := ops[1].(FloatImmediate); isFloat && imm.Value == 0 {
				b, _ = floatLiteralBits(0, w)
			} else {
				return true, "fcmp against an operand that is not a register or #0.0", false
			}
			// The flags are the IEEE comparison of the two values; every
			// condition code reads them as a predicate (floatCondition).
			state.flags = &flagsFact{left: a, right: b, width: w, float: true}
			return true, "", true
		case "mov", "dup":
			// mov sD, vN.s[k] (dup's alias): the lane into the scalar.
			n, okN := reg(1)
			if !okN || n.Class != ClassV || n.Lane < 0 || 8*laneBytes(n.Vec) != w {
				return false, "", true
			}
			lane, okL := state.readVecView(n)
			if !okL {
				return true, "unbound vector register read", false
			}
			writeScalar(d, lane)
			return true, "", true
		case "faddp":
			// faddp sD, vN.2s / dD, vN.2d: the pair's sum.
			n, okN := reg(1)
			count, bits, isArr := floatArrangement(n.Vec)
			if !okN || !isArr || count != 2 || bits != w {
				return true, "faddp over a source that is not a two-lane arrangement of the result's width", false
			}
			lanes, okL := state.laneOperands(n, n.Vec)
			if !okL {
				return true, "unbound vector register read", false
			}
			writeScalar(d, floatTerm("fadd", w, lanes[0], lanes[1]))
			return true, "", true
		}
		return false, "", true
	}
	// An integer destination from a float source: the conversions.
	if d.Class == ClassW || d.Class == ClassX {
		switch instr.Mnemonic {
		case "fcvtzs", "fcvtzu":
			n, okN := reg(1)
			if _, isN := scalarFloatWidth(n); !okN || !isN {
				return true, instr.Mnemonic + " from a source that is not a scalar float view", false
			}
			a, okA := readScalar(n)
			if !okA {
				return true, "unbound vector register read", false
			}
			state.write(d, floatTerm(instr.Mnemonic, widthOf(d.Class), a))
			return true, "", true
		}
		return false, "", true
	}
	// Lane forms over a float arrangement.
	if d.Class != ClassV || d.Lane >= 0 {
		// mov vD.s[i], vN.s[j] / mov vD.s[i], wN (ins): one lane replaced.
		if instr.Mnemonic == "mov" || instr.Mnemonic == "ins" {
			if d.Class == ClassV && d.Lane >= 0 {
				return x.insertLane(instr, state)
			}
		}
		return false, "", true
	}
	count, bits, isFloatArr := floatArrangement(d.Vec)
	switch instr.Mnemonic {
	case "fadd", "fsub", "fmul", "fdiv", "fmin", "fmax", "fminnm", "fmaxnm", "fmla", "fmls", "faddp", "fsqrt", "fneg", "fabs", "scvtf", "ucvtf", "fcvtzs", "fcvtzu":
		if !isFloatArr {
			return true, "a floating-point instruction over an arrangement without a float format (" + instr.Mnemonic + " " + d.Vec + ")", false
		}
	default:
		return false, "", true
	}
	n, okN := reg(1)
	if !okN || n.Class != ClassV || n.Vec != d.Vec {
		return true, "a floating-point lane instruction over mixed arrangements (" + instr.Mnemonic + ")", false
	}
	left, okL := state.laneOperands(n, d.Vec)
	if !okL {
		return true, "unbound vector register read", false
	}
	out := make([]*term, count)
	switch instr.Mnemonic {
	case "fsqrt", "fneg", "fabs":
		for k := range out {
			out[k], _ = floatArith(instr.Mnemonic, bits, left[k])
		}
	case "scvtf", "ucvtf", "fcvtzs", "fcvtzu":
		for k := range out {
			out[k] = floatTerm(instr.Mnemonic, bits, left[k])
		}
	default:
		m, okM := reg(2)
		if !okM || m.Class != ClassV || m.Vec != d.Vec {
			return true, "a floating-point lane instruction over mixed arrangements (" + instr.Mnemonic + ")", false
		}
		right, okR := state.laneOperands(m, d.Vec)
		if !okR {
			return true, "unbound vector register read", false
		}
		switch instr.Mnemonic {
		case "fmla", "fmls":
			// vd = vd + vn*vm (fmls: vd - vn*vm), one rounding per lane.
			acc, okAcc := state.laneOperands(d, d.Vec)
			if !okAcc {
				return true, "unbound vector register read", false
			}
			for k := range out {
				a := left[k]
				if instr.Mnemonic == "fmls" {
					a = floatNeg(a, bits)
				}
				out[k] = floatTerm("fma", bits, a, right[k], acc[k])
			}
		case "faddp":
			// Adjacent pairs of vn then of vm (Arm ARM C7.2.86): the
			// pairwise sum the reduce_add tree is built from.
			pairs := append(append([]*term{}, left...), right...)
			for k := range out {
				out[k] = floatTerm("fadd", bits, pairs[2*k], pairs[2*k+1])
			}
		default:
			for k := range out {
				out[k], _ = floatArith(instr.Mnemonic, bits, left[k], right[k])
			}
		}
	}
	state.writeLanes(d, out, bits)
	return true, "", true
}

// insertLane executes `mov vD.T[i], vN.T[j]` and `mov vD.T[i], wN|xN`
// (INS): lane i of vD replaced, the rest kept.
func (x *pathExecutor) insertLane(instr Instruction, state *symbolicState) (bool, string, bool) {
	d := instr.Operands[0].(Register)
	bits := 8 * laneBytes(d.Vec)
	if bits == 0 || bits > 64 {
		return true, "a lane insert of an unknown width", false
	}
	current, ok := state.readVec(d.Num)
	if !ok {
		return true, "unbound vector register read", false
	}
	lanes := current.lanesAt(bits)
	if d.Lane >= len(lanes) {
		return true, "a lane insert past the register", false
	}
	n, isReg := instr.Operands[1].(Register)
	if !isReg {
		return true, "a lane insert without a register source", false
	}
	var value *term
	switch {
	case n.Class == ClassV && n.Lane >= 0 && 8*laneBytes(n.Vec) == bits:
		var okN bool
		if value, okN = state.readVecView(n); !okN {
			return true, "unbound vector register read", false
		}
	case n.Class == ClassW || n.Class == ClassX:
		whole, okN := state.read(n)
		if !okN {
			return true, "unbound register read", false
		}
		value = narrowLane(whole, bits)
	default:
		return true, "a lane insert from an operand of another width", false
	}
	out := append([]*term{}, lanes...)
	out[d.Lane] = value
	state.writeVec(d.Num, vecOfLanes(out, bits))
	return true, "", true
}

// floatWitness marks a parameter name as a float of width w for the
// witness generator: beside the boundary patterns it tries ordinary
// values, so a difference in the arithmetic shows on finite operands too.
func floatWitnessValues(w int) []uint64 {
	values := []float64{0, -0.0, 1, -1, 0.5, 2, 3, 1.5, -2.5, 10, 0.1, 1e10, -1e-10, math.Inf(1), math.NaN()}
	out := make([]uint64, len(values))
	for i, v := range values {
		if w == 32 {
			out[i] = uint64(math.Float32bits(float32(v)))
		} else {
			out[i] = math.Float64bits(v)
		}
	}
	return out
}
