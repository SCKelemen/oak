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
	// memo shares the blasting of shared subterms: the terms are DAGs (a
	// loop-carried value or a local appears in every place it is read),
	// and re-blasting each reference is exponential in the nesting depth.
	memo map[*term][]int
	// grouped orders the bits of each root parameter (a record, an array,
	// a scalar) in a block of their own — the leaves of one aggregate still
	// interleaved, independent aggregates apart. The interleaved order is
	// the first choice (adders across parameters stay linear); the grouped
	// order is the second when the first exceeds the budget, since a
	// property that relates two aggregates only through their own normal
	// forms is exponential interleaved and linear grouped.
	grouped   bool
	groupBase map[string]int // parameter -> first variable of its block
	groupSize map[string]int // parameter -> parameters in its block
	groupPos  map[string]int // parameter -> position within its block
	// owners maps a parameter variable back to its parameter bit, for
	// counterexamples under either order.
	owners map[int]variableOwner
}

type variableOwner struct {
	param string
	bit   int
}

type selectAbstraction struct {
	span string
	idx  []int // canonical index bits
	vars []int // the fresh variable indices holding the value
}

const blastNodeBudget = 2000000

func newBlaster(params []string, widths map[string]int) *blaster {
	index := make(map[string]int, len(params))
	for i, name := range params {
		index[name] = i
	}
	return &blaster{bdd: newBDD(blastNodeBudget), params: params, index: index, widths: widths, owners: map[int]variableOwner{}}
}

// rootParam is the parameter a leaf belongs to: the name before the first
// field or element path (`f.op[1]` belongs to `f`; a scalar is its own root).
func rootParam(name string) string {
	for i := 0; i < len(name); i++ {
		if name[i] == '.' || name[i] == '[' {
			return name[:i]
		}
	}
	return name
}

// paramGroups counts the root parameters among the names.
func paramGroups(params []string) int {
	seen := map[string]bool{}
	for _, name := range params {
		seen[rootParam(name)] = true
	}
	return len(seen)
}

// newGroupedBlaster orders each root parameter's bits in a block of its
// own, the blocks in order of first appearance.
func newGroupedBlaster(params []string, widths map[string]int) *blaster {
	bl := newBlaster(params, widths)
	bl.grouped = true
	bl.groupBase = map[string]int{}
	bl.groupSize = map[string]int{}
	bl.groupPos = map[string]int{}
	var roots []string
	members := map[string][]string{}
	for _, name := range params {
		root := rootParam(name)
		if _, seen := members[root]; !seen {
			roots = append(roots, root)
		}
		members[root] = append(members[root], name)
	}
	base := 0
	for _, root := range roots {
		for pos, name := range members[root] {
			bl.groupBase[name] = base
			bl.groupSize[name] = len(members[root])
			bl.groupPos[name] = pos
		}
		base += 64 * len(members[root])
	}
	return bl
}

// selectSlots is the number of distinct element reads that share the
// interleaved variable order with the parameters (bit j of every operand
// adjacent — what keeps adders linear-size). Further reads take variables
// past every interleaved bit, where an adder over them may exceed the
// budget (a labeled evidence verdict, never a false proof).
const selectSlots = 8

// stride is the number of interleaved operands: parameters plus select slots.
func (bl *blaster) stride() int { return len(bl.params) + selectSlots }

// variableIndex is the ordering position of parameter bit j: interleaved
// across the parameters, or within its root's block under the grouped order.
func (bl *blaster) variableIndex(param string, bit int) int {
	var v int
	if bl.grouped {
		v = bl.groupBase[param] + bit*bl.groupSize[param] + bl.groupPos[param]
	} else {
		v = bit*bl.stride() + bl.index[param]
	}
	bl.owners[v] = variableOwner{param: param, bit: bit}
	return v
}

// selectVariable is the position of bit j of select slot s: interleaved with
// the parameters for the first slots, past every parameter bit after them
// (and always past them under the grouped order, whose parameter blocks
// fill the interleaved region).
func (bl *blaster) selectVariable(slot, bit int) int {
	if slot < selectSlots && !bl.grouped {
		return bit*bl.stride() + len(bl.params) + slot
	}
	if bl.grouped {
		return 64*bl.stride() + slot*64 + bit
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
	if bl.memo == nil {
		bl.memo = map[*term][]int{}
	}
	if cached, seen := bl.memo[t]; seen {
		return cached
	}
	out := bl.blastUncached(t)
	if out != nil {
		bl.memo[t] = out
	}
	return out
}

func (bl *blaster) blastUncached(t *term) []int {
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
	case "sar":
		if t.right.kind == termConst {
			out = shiftRightArith(left, int(t.right.value%uint64(t.width)))
		} else {
			out = bl.shiftBarrelArith(left, right)
		}
	case "mul":
		out = bl.multiply(left, right)
	case "ror":
		if t.right.kind == termConst {
			out = rotateRight(left, int(t.right.value%uint64(t.width)))
		} else {
			out = bl.rotateBarrel(left, right)
		}
	case "rev", "rev16", "rev32", "rbit":
		out = permuteBits(t.op, left)
	case "clz":
		out = bl.countLeadingZeros(left)
	case "cnt":
		out = bl.popCount(left)
	case "cls":
		// CLZ(x ^ (x >>s 1)) - 1
		shifted := shiftRightArith(left, 1)
		xor := make([]int, len(left))
		for i := range left {
			xor[i] = bl.bdd.apply(opXor, left[i], shifted[i])
		}
		ones := make([]int, len(left))
		for i := range ones {
			ones[i] = bddTrue
		}
		out = bl.add(bl.countLeadingZeros(xor), ones, bddFalse) // minus one
	default:
		// udiv, sdiv, umulh, smulh: beyond the bit-level decision (an
		// evidence verdict when reached).
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
	kind, bare := splitFlagsKind(code)
	var result []int
	var c, v int
	msb := len(left) - 1
	switch kind {
	case "add":
		// adds: the flags of left + right — C the carry out, V a signed
		// overflow (equal operand signs, a differing result sign).
		result, c = bl.addCarry(left, right, bddFalse)
		v = b.apply(opAnd, b.not(b.apply(opXor, left[msb], right[msb])), b.apply(opXor, result[msb], left[msb]))
	case "and":
		// tst: the flags of left & right; C and V are cleared.
		result = make([]int, len(left))
		for i := range left {
			result[i] = b.apply(opAnd, left[i], right[i])
		}
		c, v = bddFalse, bddFalse
	default:
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

// shiftRightArith is the arithmetic right shift by a constant: the sign
// bit fills from the top.
func shiftRightArith(a []int, k int) []int {
	out := make([]int, len(a))
	sign := a[len(a)-1]
	for i := range a {
		if i+k < len(a) {
			out[i] = a[i+k]
		} else {
			out[i] = sign
		}
	}
	return out
}

// shiftBarrelArith is the arithmetic barrel shifter: one mux stage per
// count bit, sign-filling.
func (bl *blaster) shiftBarrelArith(a, count []int) []int {
	stages := bits.Len(uint(len(a) - 1))
	current := a
	for s := 0; s < stages; s++ {
		shifted := shiftRightArith(current, 1<<uint(s))
		next := make([]int, len(a))
		for i := range a {
			next[i] = bl.bdd.ite(count[s], shifted[i], current[i])
		}
		current = next
	}
	return current
}

// multiply is the shift-and-add product modulo the width: for every set
// bit of the right operand, the left operand shifted into place is added.
// Two symbolic operands are BDD-hard (the budget yields an evidence
// verdict); a constant operand folds to shifted adds.
func (bl *blaster) multiply(a, b []int) []int {
	out := make([]int, len(a))
	for i := range out {
		out[i] = bddFalse
	}
	for i := range b {
		if b[i] == bddFalse {
			continue
		}
		partial := shiftConst(a, i, true)
		for j := range partial {
			partial[j] = bl.bdd.apply(opAnd, partial[j], b[i])
		}
		out = bl.add(out, partial, bddFalse)
		if bl.bdd.exceeded {
			return out
		}
	}
	return out
}

// rotateRight rotates by a constant.
func rotateRight(a []int, k int) []int {
	n := len(a)
	out := make([]int, n)
	for i := range a {
		out[i] = a[(i+k)%n]
	}
	return out
}

// rotateBarrel rotates by a term count reduced modulo the width.
func (bl *blaster) rotateBarrel(a, count []int) []int {
	stages := bits.Len(uint(len(a) - 1))
	current := a
	for s := 0; s < stages; s++ {
		rotated := rotateRight(current, 1<<uint(s))
		next := make([]int, len(a))
		for i := range a {
			next[i] = bl.bdd.ite(count[s], rotated[i], current[i])
		}
		current = next
	}
	return current
}

// permuteBits realizes the byte and bit reversals as bit permutations.
func permuteBits(op string, a []int) []int {
	n := len(a)
	out := make([]int, n)
	for i := range a {
		var src int
		switch op {
		case "rbit":
			src = n - 1 - i
		case "rev":
			byteIndex, bit := i/8, i%8
			src = (n/8-1-byteIndex)*8 + bit
		case "rev16":
			half, within := i/16, i%16
			byteIndex, bit := within/8, within%8
			src = half*16 + (1-byteIndex)*8 + bit
		case "rev32":
			word, within := i/32, i%32
			byteIndex, bit := within/8, within%8
			src = word*32 + (3-byteIndex)*8 + bit
		}
		out[i] = a[src]
	}
	return out
}

// countLeadingZeros is a priority encoder: the count is the number of
// leading bits before the highest set bit, width when none is set.
// popCount is the number of set bits, at the operand's width: each bit is
// widened to a word and the words are summed by the adder; the count is
// at most the width, so no sum wraps.
func (bl *blaster) popCount(a []int) []int {
	n := len(a)
	total := make([]int, n)
	for i := range total {
		total[i] = bddFalse
	}
	for _, bit := range a {
		one := make([]int, n)
		one[0] = bit
		for i := 1; i < n; i++ {
			one[i] = bddFalse
		}
		total = bl.add(total, one, bddFalse)
	}
	return total
}

func (bl *blaster) countLeadingZeros(a []int) []int {
	n := len(a)
	b := bl.bdd
	// prefixZero[i]: bits above and including position i are all zero.
	result := make([]int, n)
	for i := range result {
		result[i] = bddFalse
	}
	setConst := func(value int) []int {
		bits := make([]int, n)
		for i := range bits {
			bits[i] = bddFalse
			if (value>>uint(i))&1 == 1 {
				bits[i] = bddTrue
			}
		}
		return bits
	}
	// Scan from the top: result = ite(a[top] , 0, ite(a[top-1], 1, ...)).
	acc := setConst(n) // all zero
	for pos := 0; pos < n; pos++ {
		candidate := setConst(n - 1 - pos)
		next := make([]int, n)
		for i := range next {
			next[i] = b.ite(a[pos], candidate[i], acc[i])
		}
		acc = next
	}
	return acc
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
		owner, isParam := bl.owners[variable]
		if !value || !isParam {
			continue // select variables have no parameter to report
		}
		env[owner.param] |= uint64(1) << uint(owner.bit)
	}
	return env
}
