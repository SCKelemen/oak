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
	// selects are the uninterpreted element reads met so far: a select at
	// an index whose bits are the same canonical nodes as an earlier one
	// (over the same span) is the same value and shares its variables.
	selects []selectAbstraction
}

type selectAbstraction struct {
	span string
	idx  []int // canonical index bits
	vars []int // the fresh variable indices holding the value
}

const blastNodeBudget = 400000

func newBlaster(params []string, widths map[string]int) *blaster {
	index := make(map[string]int, len(params))
	for i, name := range params {
		index[name] = i
	}
	return &blaster{bdd: newBDD(blastNodeBudget), params: params, index: index, widths: widths}
}

// selectSlots is the number of distinct element reads that share the
// interleaved variable order with the parameters (bit j of every operand
// adjacent — what keeps adders linear-size). Further reads take variables
// past every interleaved bit, where an adder over them may exceed the
// budget (a labeled evidence verdict, never a false proof).
const selectSlots = 8

// stride is the number of interleaved operands: parameters plus select slots.
func (bl *blaster) stride() int { return len(bl.params) + selectSlots }

// variableIndex is the interleaved ordering position of parameter bit j.
func (bl *blaster) variableIndex(param string, bit int) int {
	return bit*bl.stride() + bl.index[param]
}

// selectVariable is the interleaved position of bit j of select slot s.
func (bl *blaster) selectVariable(slot, bit int) int {
	if slot < selectSlots {
		return bit*bl.stride() + len(bl.params) + slot
	}
	return 64*bl.stride() + (slot-selectSlots)*64 + bit
}

// selectBits abstracts a select as fresh variables — one block per distinct
// (span, index) — sound for equality proofs: terms equal under independent
// element values are equal under every memory.
func (bl *blaster) selectBits(span string, idx []int, width int) []int {
	for _, known := range bl.selects {
		if known.span != span || len(known.idx) != len(idx) {
			continue
		}
		same := true
		for i := range idx {
			if idx[i] != known.idx[i] {
				same = false
				break
			}
		}
		if same {
			return bl.varsBits(known.vars, width)
		}
	}
	slot := len(bl.selects)
	vars := make([]int, width)
	for i := range vars {
		vars[i] = bl.selectVariable(slot, i)
	}
	bl.selects = append(bl.selects, selectAbstraction{span: span, idx: idx, vars: vars})
	return bl.varsBits(vars, width)
}

func (bl *blaster) varsBits(vars []int, width int) []int {
	out := make([]int, width)
	for i := range out {
		if i < len(vars) {
			out[i] = bl.bdd.variable(vars[i])
		} else {
			out[i] = bddFalse
		}
	}
	return out
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
	case termSelect:
		idx := bl.adapt(bl.blast(t.left), 32)
		if idx == nil {
			return nil
		}
		return bl.selectBits(t.name, idx, t.width)
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
	add, bare := splitFlagsKind(code)
	var result []int
	var c, v int
	msb := len(left) - 1
	if add {
		// adds: the flags of left + right — C the carry out, V a signed
		// overflow (equal operand signs, a differing result sign).
		result, c = bl.addCarry(left, right, bddFalse)
		v = b.apply(opAnd, b.not(b.apply(opXor, left[msb], right[msb])), b.apply(opXor, result[msb], left[msb]))
	} else {
		negated := make([]int, len(right))
		for i := range right {
			negated[i] = b.not(right[i])
		}
		result, c = bl.addCarry(left, negated, bddTrue)
		v = b.apply(opAnd, b.apply(opXor, left[msb], right[msb]), b.apply(opXor, result[msb], left[msb]))
	}
	n := result[msb]
	z := bddTrue
	for _, bit := range result {
		z = b.apply(opAnd, z, b.not(bit))
	}
	nEqV := b.not(b.apply(opXor, n, v))
	switch bare {
	case "eq":
		return z
	case "ne":
		return b.not(z)
	case "hs", "cs":
		return c
	case "lo", "cc":
		return b.not(c)
	case "mi":
		return n
	case "pl":
		return b.not(n)
	case "vs":
		return v
	case "vc":
		return b.not(v)
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
		position := variable % bl.stride()
		if !value || variable >= 64*bl.stride() || position >= len(bl.params) {
			continue // select variables have no parameter to report
		}
		param := bl.params[position]
		bit := variable / bl.stride()
		env[param] |= uint64(1) << uint(bit)
	}
	return env
}
