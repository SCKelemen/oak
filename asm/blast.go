package asm

// Bit-blasting for the §8 verifier: a term becomes one BDD per result bit
// over the parameters' bits. Parameters are variables in an interleaved
// order (bit j of every parameter adjacent, so ripple-carry adders stay
// linear-size); constants are terminals; and/or/xor are pointwise; add is
// a ripple-carry chain; sub adds the two's complement; shifts by a constant
// reindex bits and shifts by a term are a barrel of muxes over the count's
// low bits (the machine reduces the count modulo the width, as eval does);
// mask nodes are pointwise ands with a constant. Two blasted terms are
// equal exactly when every bit is the same canonical node
// (Oak.AssemblerSemantics.eq_of_bits).

import (
	"math/bits"
)

type blaster struct {
	bdd    *bdd
	params []string       // parameter order
	index  map[string]int // parameter -> position
	widths map[string]int // parameter -> declared width
}

const blastNodeBudget = 400000

func newBlaster(params []string, widths map[string]int) *blaster {
	index := make(map[string]int, len(params))
	for i, name := range params {
		index[name] = i
	}
	return &blaster{bdd: newBDD(blastNodeBudget), params: params, index: index, widths: widths}
}

// variableIndex is the interleaved ordering position of parameter bit j.
func (bl *blaster) variableIndex(param string, bit int) int {
	return bit*len(bl.params) + bl.index[param]
}

// blast returns width nodes (LSB first), or nil when the budget is exceeded.
func (bl *blaster) blast(t *term) []int {
	if bl.bdd.exceeded {
		return nil
	}
	out := make([]int, t.width)
	switch t.kind {
	case termConst:
		for i := 0; i < t.width; i++ {
			out[i] = bddFalse
			if (t.value>>uint(i))&1 == 1 {
				out[i] = bddTrue
			}
		}
		return out
	case termParam:
		declared := bl.widths[t.name]
		for i := 0; i < t.width; i++ {
			if i < declared {
				out[i] = bl.bdd.variable(bl.variableIndex(t.name, i))
			} else {
				out[i] = bddFalse // zero-extension of a narrower parameter
			}
		}
		return out
	case termCmp:
		// The comparison is the flag reading of `left - right` at the
		// operands' width: NZCV from the subtraction chain, then the ARM
		// condition table (Oak.AssemblerSemantics.condHolds).
		left := bl.blast(t.left)
		right := bl.blast(t.right)
		if left == nil || right == nil {
			return nil
		}
		holds := bl.condition(t.op, left, right)
		for i := range out {
			out[i] = bddFalse
		}
		out[0] = holds
		return out
	case termIte:
		cond := bl.blast(t.cond)
		left := bl.adapt(bl.blast(t.left), t.width)
		right := bl.adapt(bl.blast(t.right), t.width)
		if cond == nil || left == nil || right == nil {
			return nil
		}
		for i := range out {
			out[i] = bl.bdd.ite(cond[0], left[i], right[i])
		}
		if bl.bdd.exceeded {
			return nil
		}
		return out
	}
	left := bl.adapt(bl.blast(t.left), t.width)
	right := bl.adapt(bl.blast(t.right), t.width)
	if left == nil || right == nil {
		return nil
	}
	switch t.op {
	case "and", "or", "xor":
		op := map[string]int{"and": opAnd, "or": opOr, "xor": opXor}[t.op]
		for i := range out {
			out[i] = bl.bdd.apply(op, left[i], right[i])
		}
	case "add":
		out = bl.add(left, right, bddFalse)
	case "sub":
		negated := make([]int, len(right))
		for i := range right {
			negated[i] = bl.bdd.not(right[i])
		}
		out = bl.add(left, negated, bddTrue)
	case "shl", "shr":
		if t.right.kind == termConst {
			out = shiftConst(left, int(t.right.value%uint64(t.width)), t.op == "shl")
		} else {
			out = bl.shiftBarrel(left, right, t.op == "shl")
		}
	default:
		return nil
	}
	if bl.bdd.exceeded {
		return nil
	}
	return out
}

// adapt zero-extends or truncates operand bits to the term width, exactly
// as eval masks operands to the term's width.
func (bl *blaster) adapt(bitsIn []int, width int) []int {
	if bitsIn == nil {
		return nil
	}
	if len(bitsIn) == width {
		return bitsIn
	}
	out := make([]int, width)
	for i := 0; i < width; i++ {
		if i < len(bitsIn) {
			out[i] = bitsIn[i]
		} else {
			out[i] = bddFalse
		}
	}
	return out
}

// add is the ripple-carry chain: sum_i = a_i ⊕ b_i ⊕ c_i,
// c_{i+1} = (a_i ∧ b_i) ∨ (c_i ∧ (a_i ⊕ b_i)) — `Oak.AssemblerSemantics.
// rippleCarry`, proved equal to `BitVec.carry` so that `rippleSum` is
// exactly `BitVec.add` bit by bit.
func (bl *blaster) add(a, b []int, carry int) []int {
	out, _ := bl.addCarry(a, b, carry)
	return out
}

// addCarry is the chain with its carry-out — the C flag of the machine.
func (bl *blaster) addCarry(a, b []int, carry int) ([]int, int) {
	out := make([]int, len(a))
	for i := range a {
		axb := bl.bdd.apply(opXor, a[i], b[i])
		out[i] = bl.bdd.apply(opXor, axb, carry)
		carry = bl.bdd.apply(opOr, bl.bdd.apply(opAnd, a[i], b[i]), bl.bdd.apply(opAnd, carry, axb))
	}
	return out, carry
}

// condition computes a condition code over the NZCV flags of `left -
// right` (the machine's cmp: left + ~right + 1). N is the result's sign bit,
// Z its zero test, C the chain's carry-out (no borrow), V the signed
// overflow of a subtraction (operand signs differ and the result's sign
// differs from left's). The condition table is ARM's, transliterated from
// Oak.AssemblerSemantics.condHolds.
func (bl *blaster) condition(code string, left, right []int) int {
	b := bl.bdd
	negated := make([]int, len(right))
	for i := range right {
		negated[i] = b.not(right[i])
	}
	diff, c := bl.addCarry(left, negated, bddTrue)
	msb := len(diff) - 1
	n := diff[msb]
	z := bddTrue
	for _, bit := range diff {
		z = b.apply(opAnd, z, b.not(bit))
	}
	v := b.apply(opAnd, b.apply(opXor, left[msb], right[msb]), b.apply(opXor, diff[msb], left[msb]))
	nEqV := b.not(b.apply(opXor, n, v))
	switch code {
	case "eq":
		return z
	case "ne":
		return b.not(z)
	case "hs", "cs":
		return c
	case "lo", "cc":
		return b.not(c)
	case "hi":
		return b.apply(opAnd, c, b.not(z))
	case "ls":
		return b.apply(opOr, b.not(c), z)
	case "ge":
		return nEqV
	case "lt":
		return b.not(nEqV)
	case "gt":
		return b.apply(opAnd, b.not(z), nEqV)
	case "le":
		return b.apply(opOr, z, b.not(nEqV))
	}
	return bddFalse
}

func shiftConst(a []int, k int, left bool) []int {
	out := make([]int, len(a))
	for i := range a {
		out[i] = bddFalse
		if left {
			if i-k >= 0 {
				out[i] = a[i-k]
			}
		} else if i+k < len(a) {
			out[i] = a[i+k]
		}
	}
	return out
}

// shiftBarrel shifts by a term count reduced modulo the width: one mux
// stage per count bit.
func (bl *blaster) shiftBarrel(a, count []int, left bool) []int {
	stages := bits.Len(uint(len(a) - 1))
	current := a
	for s := 0; s < stages; s++ {
		shifted := shiftConst(current, 1<<uint(s), left)
		next := make([]int, len(a))
		for i := range a {
			next[i] = bl.bdd.ite(count[s], shifted[i], current[i])
		}
		current = next
	}
	return current
}

// counterexample turns a differing bit into a concrete parameter assignment.
func (bl *blaster) counterexample(x, y int) map[string]uint64 {
	diff := bl.bdd.apply(opXor, x, y)
	assignment := bl.bdd.satisfyingPath(diff)
	env := make(map[string]uint64, len(bl.params))
	for variable, value := range assignment {
		if !value {
			continue
		}
		param := bl.params[variable%len(bl.params)]
		bit := variable / len(bl.params)
		env[param] |= uint64(1) << uint(bit)
	}
	return env
}
