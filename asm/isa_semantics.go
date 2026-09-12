package asm

// Verifier semantics for the general-purpose ISA (asm/isa.go): every
// instruction whose result is a bitvector function of its operands lowers
// to the term language; ordering, exclusivity, exceptions, and indirect
// transfers are outside the subset and reported so.

import (
	"fmt"
	"math/bits"
)

// stepISA executes one instruction of the extended set. handled is false
// when the instruction belongs to the core executor.
func stepISA(instr Instruction, state *symbolicState) (handled bool, reason string, ok bool) {
	name := instr.Mnemonic
	dest := func() Register { return instr.Operands[0].(Register) }
	width := func() int { return widthOf(dest().Class) }
	operand := func(i int, w int) (*term, bool) { return operandTerm(state, instr.Operands[i], w) }
	switch name {
	case "adc", "sbc", "adcs", "sbcs", "ngc", "ngcs":
		if state.flags == nil || state.flags.unknown {
			return true, name + " reading flags not produced by cmp/subs/adds", false
		}
		w := width()
		carry := adaptWidth(flagsCondition("cs", state.flags), w)
		var a, b *term
		var okA, okB bool
		if name == "ngc" || name == "ngcs" {
			a, okA = constTerm(0, w), true
			b, okB = operand(1, w)
		} else {
			a, okA = operand(1, w)
			b, okB = operand(2, w)
		}
		if !okA || !okB {
			return true, "unbound register read", false
		}
		var value *term
		if name == "adc" || name == "adcs" {
			value = binaryTerm("add", binaryTerm("add", a, b), carry)
		} else {
			// sbc: a - b - (1 - C)
			value = binaryTerm("sub", binaryTerm("sub", a, b), binaryTerm("xor", carry, constTerm(1, w)))
		}
		if name == "adcs" || name == "sbcs" || name == "ngcs" {
			state.flags = &flagsFact{unknown: true} // a carry-in chain's flags are not one comparison
		}
		state.write(dest(), value)
		return true, "", true
	case "cmn":
		left := instr.Operands[0].(Register)
		w := widthOf(left.Class)
		l, okL := operandTerm(state, left, w)
		r, okR := operand(1, w)
		if !okL || !okR {
			return true, "unbound register read", false
		}
		state.flags = &flagsFact{left: l, right: r, width: w, kind: "add"}
		return true, "", true
	case "ccmn":
		if state.flags == nil || state.flags.unknown {
			return true, "ccmn reading flags not produced by cmp/subs", false
		}
		code := instr.Operands[3].(Condition).Code
		if !verifiableConditions[code] {
			return true, fmt.Sprintf("condition code %s", code), false
		}
		left := instr.Operands[0].(Register)
		w := widthOf(left.Class)
		l, okL := operandTerm(state, left, w)
		r, okR := operand(1, w)
		if !okL || !okR {
			return true, "unbound register read", false
		}
		prior := flagsCondition(code, state.flags)
		state.flags = &flagsFact{left: l, right: r, width: w, kind: "add", cond: prior, elseNZCV: instr.Operands[2].(Immediate).Value}
		return true, "", true
	case "ands", "bic", "bics", "orn", "eon", "negs":
		w := width()
		if name == "negs" {
			b, okB := operand(1, w)
			if !okB {
				return true, "unbound register read", false
			}
			state.flags = &flagsFact{left: constTerm(0, w), right: b, width: w}
			state.write(dest(), binaryTerm("sub", constTerm(0, w), b))
			return true, "", true
		}
		a, okA := operand(1, w)
		b, okB := operand(2, w)
		if !okA || !okB {
			return true, "unbound register read", false
		}
		var value *term
		switch name {
		case "ands":
			value = binaryTerm("and", a, b)
			state.flags = &flagsFact{left: a, right: b, width: w, kind: "and"}
		case "bic", "bics":
			notB := binaryTerm("xor", b, constTerm(mask(w), w))
			value = binaryTerm("and", a, notB)
			if name == "bics" {
				state.flags = &flagsFact{left: a, right: notB, width: w, kind: "and"}
			}
		case "orn":
			value = binaryTerm("or", a, binaryTerm("xor", b, constTerm(mask(w), w)))
		case "eon":
			value = binaryTerm("xor", a, binaryTerm("xor", b, constTerm(mask(w), w)))
		}
		state.write(dest(), value)
		return true, "", true
	case "ror":
		w := width()
		a, okA := operand(1, w)
		b, okB := operand(2, w)
		if !okA || !okB {
			return true, "unbound register read", false
		}
		state.write(dest(), binaryTerm("ror", a, b))
		return true, "", true
	case "extr":
		w := width()
		hi, okH := operand(1, w)
		lo, okL := operand(2, w)
		if !okH || !okL {
			return true, "unbound register read", false
		}
		lsb := instr.Operands[3].(Immediate).Value
		if lsb == 0 {
			state.write(dest(), lo)
			return true, "", true
		}
		value := binaryTerm("or", binaryTerm("shr", lo, constTerm(uint64(lsb), w)), binaryTerm("shl", hi, constTerm(uint64(int64(w)-lsb), w)))
		state.write(dest(), value)
		return true, "", true
	case "rev", "rev16", "rev32", "rbit", "clz", "cls":
		w := width()
		a, okA := operand(1, w)
		if !okA {
			return true, "unbound register read", false
		}
		state.write(dest(), binaryTerm(name, a, constTerm(0, w)))
		return true, "", true
	case "sxtb", "sxth", "sxtw", "uxtb", "uxth":
		w := width()
		var from int
		switch name {
		case "sxtb", "uxtb":
			from = 8
		case "sxth", "uxth":
			from = 16
		default:
			from = 32
		}
		source, okS := operandTerm(state, instr.Operands[1], w)
		if !okS {
			return true, "unbound register read", false
		}
		state.write(dest(), extendTerm(source, from, w, name[0] == 's'))
		return true, "", true
	case "movz", "movn", "movk":
		w := width()
		imm := instr.Operands[1].(Immediate)
		if imm.Value < 0 || imm.Value > 0xFFFF {
			return true, "a wide-move immediate beyond 16 bits", false
		}
		placed := uint64(imm.Value) << uint(imm.Shift)
		switch name {
		case "movz":
			state.write(dest(), constTerm(placed, w))
		case "movn":
			state.write(dest(), constTerm(^placed, w))
		case "movk":
			current, okC := state.read(dest())
			if !okC {
				return true, "unbound register read", false
			}
			hole := constTerm(^(uint64(0xFFFF) << uint(imm.Shift)), w)
			state.write(dest(), binaryTerm("or", binaryTerm("and", current, hole), constTerm(placed, w)))
		}
		return true, "", true
	case "csinc", "csinv", "csneg", "cinv", "csetm":
		if state.flags == nil || state.flags.unknown {
			return true, name + " reading flags not produced by cmp/subs", false
		}
		code := instr.Operands[len(instr.Operands)-1].(Condition).Code
		if !verifiableConditions[code] {
			return true, fmt.Sprintf("condition code %s", code), false
		}
		w := width()
		cond := flagsCondition(code, state.flags)
		allOnes := constTerm(mask(w), w)
		switch name {
		case "csetm":
			state.write(dest(), iteTerm(cond, allOnes, constTerm(0, w)))
		case "cinv":
			a, okA := operand(1, w)
			if !okA {
				return true, "unbound register read", false
			}
			state.write(dest(), iteTerm(cond, binaryTerm("xor", a, allOnes), a))
		default:
			a, okA := operand(1, w)
			b, okB := operand(2, w)
			if !okA || !okB {
				return true, "unbound register read", false
			}
			var other *term
			switch name {
			case "csinc":
				other = binaryTerm("add", b, constTerm(1, w))
			case "csinv":
				other = binaryTerm("xor", b, allOnes)
			default:
				other = binaryTerm("sub", constTerm(0, w), b)
			}
			state.write(dest(), iteTerm(cond, a, other))
		}
		return true, "", true
	case "smull", "umull", "smaddl", "umaddl", "smsubl", "umsubl":
		n, okN := operandTerm(state, instr.Operands[1], 32)
		m, okM := operandTerm(state, instr.Operands[2], 32)
		if !okN || !okM {
			return true, "unbound register read", false
		}
		signed := name[0] == 's'
		product := binaryTerm("mul", extendTerm(n, 32, 64, signed), extendTerm(m, 32, 64, signed))
		switch name {
		case "smull", "umull":
			state.write(dest(), product)
		default:
			a, okA := operand(3, 64)
			if !okA {
				return true, "unbound register read", false
			}
			if name == "smaddl" || name == "umaddl" {
				state.write(dest(), binaryTerm("add", a, product))
			} else {
				state.write(dest(), binaryTerm("sub", a, product))
			}
		}
		return true, "", true
	case "smulh", "umulh", "udiv", "sdiv", "mneg":
		w := width()
		a, okA := operand(1, w)
		b, okB := operand(2, w)
		if !okA || !okB {
			return true, "unbound register read", false
		}
		if name == "mneg" {
			state.write(dest(), binaryTerm("sub", constTerm(0, w), binaryTerm("mul", a, b)))
		} else {
			state.write(dest(), binaryTerm(name, a, b))
		}
		return true, "", true
	case "crc32b", "crc32h", "crc32w", "crc32x", "crc32cb", "crc32ch", "crc32cw", "crc32cx":
		return true, "a CRC step", false
	case "cfinv":
		return true, "cfinv", false
	case "br", "blr", "brk", "svc", "hvc", "smc":
		return true, name + " (control leaves the verified body)", false
	case "wfe", "wfi", "sev", "sevl", "yield", "csdb", "esb", "hint", "clrex", "dc", "ic", "tlbi", "at", "prfm":
		if name == "prfm" || name == "dc" || name == "ic" || name == "tlbi" || name == "at" {
			return true, name + " (a maintenance operation)", false
		}
		return true, "", true // hints have no value semantics
	}
	if isAtomic(name) || isExclusiveStore(name) {
		return true, name + " (an atomic access: ordering and exclusivity are outside the subset)", false
	}
	switch name {
	case "ldar", "ldxr", "ldaxr", "ldapr", "ldarb", "ldxrb", "ldaxrb", "ldaprb", "ldarh", "ldxrh", "ldaxrh", "ldaprh", "stlr", "stlrb", "stlrh", "ldpsw",
		"ldapur", "ldapurb", "ldapurh", "ldapursb", "ldapursh", "ldapursw", "stlur", "stlurb", "stlurh":
		return true, name + " (an ordered access is outside the subset)", false
	}
	return false, "", false
}

// extendTerm zero- or sign-extends the low `from` bits of a term to width.
func extendTerm(t *term, from, width int, signed bool) *term {
	low := binaryTerm("and", adaptWidth(t, width), constTerm(mask(from), width))
	if !signed {
		return low
	}
	shift := constTerm(uint64(width-from), width)
	return binaryTerm("sar", binaryTerm("shl", low, shift), shift)
}

// evalUnary evaluates the bit-manipulation operations on a value.
func evalUnary(op string, x uint64, width int) uint64 {
	m := mask(width)
	x &= m
	switch op {
	case "rev":
		if width == 32 {
			return uint64(bits.ReverseBytes32(uint32(x)))
		}
		return bits.ReverseBytes64(x)
	case "rev16":
		var out uint64
		for i := 0; i < width/16; i++ {
			half := (x >> uint(16*i)) & 0xFFFF
			out |= uint64(bits.ReverseBytes16(uint16(half))) << uint(16*i)
		}
		return out
	case "rev32":
		lo := uint64(bits.ReverseBytes32(uint32(x)))
		hi := uint64(bits.ReverseBytes32(uint32(x >> 32)))
		return lo | hi<<32
	case "rbit":
		if width == 32 {
			return uint64(bits.Reverse32(uint32(x)))
		}
		return bits.Reverse64(x)
	case "clz":
		if width == 32 {
			return uint64(bits.LeadingZeros32(uint32(x)))
		}
		return uint64(bits.LeadingZeros64(x))
	case "cnt":
		// Population count at the operand width (x is already masked).
		return uint64(bits.OnesCount64(x))
	case "cls":
		// Leading bits equal to the sign bit, minus one: CLZ(x ^ (x >>s 1)) - 1.
		shift := uint(64 - width)
		signExtended := int64(x<<shift) >> shift
		xor := (uint64(signExtended) ^ uint64(signExtended>>1)) & m
		return evalUnary("clz", xor, width) - 1
	}
	return 0
}

// evalBinaryExtra evaluates rotate, division, and high multiply.
func evalBinaryExtra(op string, l, r uint64, width int) (uint64, bool) {
	m := mask(width)
	l, r = l&m, r&m
	switch op {
	case "rv.div", "rv.divu", "rv.rem", "rv.remu":
		return rv64Divide(op, l, r, width), true
	case "ror":
		count := uint(r % uint64(width))
		if width == 32 {
			return uint64(bits.RotateLeft32(uint32(l), -int(count))), true
		}
		return bits.RotateLeft64(l, -int(count)), true
	case "udiv":
		if r == 0 {
			return 0, true // the machine's total division
		}
		return (l / r) & m, true
	case "sdiv":
		shift := uint(64 - width)
		sl, sr := int64(l<<shift)>>shift, int64(r<<shift)>>shift
		if sr == 0 {
			return 0, true
		}
		if sl == -1<<(width-1) && sr == -1 {
			return uint64(sl) & m, true // overflow wraps to the minimum
		}
		return uint64(sl/sr) & m, true
	case "umulh":
		hi, _ := bits.Mul64(l, r)
		if width == 32 {
			return (l * r) >> 32, true
		}
		return hi, true
	case "smulh":
		if width == 32 {
			return uint64(int64(int32(l))*int64(int32(r))) >> 32 & m, true
		}
		hi, lo := bits.Mul64(l, r)
		_ = lo
		// Signed high product from the unsigned one: subtract the sign terms.
		if int64(l) < 0 {
			hi -= r
		}
		if int64(r) < 0 {
			hi -= l
		}
		return hi, true
	}
	return 0, false
}

// rv64Divide is RISC-V's total division (Oak.RiscV.div and its kin): a
// zero divisor yields all ones for the quotient and the dividend for the
// remainder; the signed overflow (most negative / -1) yields the dividend
// and remainder 0.
func rv64Divide(op string, l, r uint64, width int) uint64 {
	m := mask(width)
	shift := uint(64 - width)
	sl, sr := int64(l<<shift)>>shift, int64(r<<shift)>>shift
	switch op {
	case "rv.divu":
		if r == 0 {
			return m
		}
		return (l / r) & m
	case "rv.remu":
		if r == 0 {
			return l
		}
		return (l % r) & m
	case "rv.div":
		if r == 0 {
			return m
		}
		if sr == -1 && uint64(sl)&m == (uint64(1)<<uint(width-1))&m {
			return l
		}
		return uint64(sl/sr) & m
	default: // rv.rem
		if r == 0 {
			return l
		}
		if sr == -1 {
			return 0
		}
		return uint64(sl%sr) & m
	}
}
