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
	"os"
	"strconv"
)

type blaster struct {
	bdd *bdd
	// cnf, when set, replaces the diagram engine with the clause engine
	// (asm/cnf.go): the same lowering, Tseitin clauses instead of nodes.
	cnf    *cnfBuilder
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
	label     string         // how the grouped order was chosen, for the verdict
	groupBase map[string]int // parameter -> first variable of its block
	groupSize map[string]int // parameter -> parameters in its block
	groupPos  map[string]int // parameter -> position within its block
	// lastBase and lastSize are the last block's first variable and
	// parameter count: the first select slots interleave with that block
	// (the data parameters, under the control-first orders), so a
	// comparison of a parameter with an element read stays linear.
	lastBase, lastSize int
	// owners maps a parameter variable back to its parameter bit, for
	// counterexamples under either order.
	owners map[int]variableOwner
	// assume, when assumed is set, is a diagram the decision holds under
	// (an implication's premise, a case split's condition): an ite whose
	// condition the assumption implies or refutes blasts as that arm
	// alone, so a branch on a condition over many inputs never multiplies
	// its arms' diagrams.
	assume  int
	assumed bool
	pruned  int // branches the assumption settled (trace)
}

type variableOwner struct {
	param string
	bit   int
}

type selectAbstraction struct {
	span  string
	idx   []int // canonical index bits
	vars  []int // the fresh variable indices holding the value
	index *term // the index term (nil for an uninterpreted operation's operand)
}

const blastNodeBudget = 2000000

// NodeBudget is the decider's node budget, which the Oak solver is sized to.
const NodeBudget = blastNodeBudget

// escalationTermNodes bounds the equalities that may claim the escalated
// budget (escalatedNodeBudget): a few hundred term nodes whose diagrams
// still exceed blastNodeBudget under every order — the 64-bit address
// arithmetic of a page-table walk. A large term past the budget stays
// evidence, as before.
const escalationTermNodes = 400

// escalatedNodeBudget is the node budget a build opts into for small
// equalities past the base budget: OAK_VERIFY_BUDGET=high is eight times
// the base (sixteen million nodes, where the OS pilot's translate and
// unmap_page close at eleven million), a number is that many nodes, and
// unset or 0 is no retry — the default, so a corpus of evidence verdicts
// does not pay the retry's time at every decision. The verdict cache keys
// on the setting (compiler/verdict_cache.go).
func escalatedNodeBudget() int {
	switch value := os.Getenv("OAK_VERIFY_BUDGET"); value {
	case "", "0", "base":
		return 0
	case "high":
		return 8 * blastNodeBudget
	default:
		n, err := strconv.Atoi(value)
		if err != nil || n <= blastNodeBudget {
			return 0
		}
		return n
	}
}

// withBudget gives the blaster a fresh diagram store of the budget.
func (bl *blaster) withBudget(budget int) *blaster {
	bl.bdd = newBDD(budget)
	return bl
}

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
	return newBlockedBlaster(params, widths, rootParam, nil, "parameters in blocks")
}

// newControlFirstBlaster orders the control parameters — those a
// comparison, a conditional, or a shift count reads — in a first block and
// the data parameters after them. Once the control bits are read the
// residual is one of few data functions (a selection resolved), so a
// property over several selectors compared to constants or to one another,
// exponential under either interleaving, is linear here.
func newControlFirstBlaster(params []string, widths map[string]int, control map[string]bool) *blaster {
	role := func(name string) string {
		if control[name] {
			return "control"
		}
		return "data"
	}
	return newBlockedBlaster(params, widths, role, []string{"control", "data"}, "control bits first")
}

// newSelectorFirstBlaster interleaves the parameters' bits with the
// selectors — the parameters a conditional's condition reads directly
// (selectorParams) — first at every bit. A read of an array at a loop's
// index is a conditional chain over the index with the elements in its
// arms: with the index's bit read before the elements' at each level, the
// diagram narrows the arms as it goes and stays linear in the elements,
// where reading the elements first must remember which of them is which —
// exponential in their count. The interleaving is kept (a block of the
// selectors apart would make an adder over one of them exponential).
func newSelectorFirstBlaster(params []string, widths map[string]int, selectors map[string]bool) *blaster {
	ordered := make([]string, 0, len(params))
	for _, name := range params {
		if selectors[name] {
			ordered = append(ordered, name)
		}
	}
	for _, name := range params {
		if !selectors[name] {
			ordered = append(ordered, name)
		}
	}
	bl := newBlaster(ordered, widths)
	bl.label = "selectors first"
	return bl
}

// newBlockedBlaster orders the parameters in blocks by groupOf, the blocks
// in the order given (or of first appearance), the bits of a block's
// parameters interleaved.
func newBlockedBlaster(params []string, widths map[string]int, groupOf func(string) string, order []string, label string) *blaster {
	bl := newBlaster(params, widths)
	bl.grouped = true
	bl.label = label
	bl.groupBase = map[string]int{}
	bl.groupSize = map[string]int{}
	bl.groupPos = map[string]int{}
	var groups []string
	members := map[string][]string{}
	for _, name := range params {
		group := groupOf(name)
		if _, seen := members[group]; !seen {
			groups = append(groups, group)
		}
		members[group] = append(members[group], name)
	}
	if order != nil {
		groups = groups[:0]
		for _, group := range order {
			if _, present := members[group]; present {
				groups = append(groups, group)
			}
		}
	}
	base := 0
	for i, group := range groups {
		for pos, name := range members[group] {
			bl.groupBase[name] = base
			bl.groupSize[name] = len(members[group])
			bl.groupPos[name] = pos
		}
		if i == len(groups)-1 {
			bl.lastBase, bl.lastSize = base, len(members[group])
		}
		base += 64 * len(members[group])
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
		size := bl.groupSize[param]
		if base := bl.groupBase[param]; base == bl.lastBase {
			size += selectSlots // the last block carries the select slots
		}
		v = bl.groupBase[param] + bit*size + bl.groupPos[param]
	} else {
		v = bit*bl.stride() + bl.index[param]
	}
	bl.owners[v] = variableOwner{param: param, bit: bit}
	return v
}

// selectVariable is the position of bit j of select slot s: interleaved with
// the parameters for the first slots (under the grouped order, with the
// last block's), past every parameter bit after them.
func (bl *blaster) selectVariable(slot, bit int) int {
	if bl.grouped {
		size := bl.lastSize + selectSlots
		if slot < selectSlots {
			return bl.lastBase + bit*size + bl.lastSize + slot
		}
		return bl.lastBase + 64*size + (slot-selectSlots)*64 + bit
	}
	if slot < selectSlots {
		return bit*bl.stride() + len(bl.params) + slot
	}
	return 64*bl.stride() + (slot-selectSlots)*64 + bit
}

// selectBits abstracts a select as fresh variables — one block per distinct
// (span, index) — sound for equality proofs: terms equal under independent
// element values are equal under every memory.
func (bl *blaster) selectBits(span string, idx []int, width int, index *term) []int {
	var form *linearForm
	if index != nil {
		form = index.linearAt(32)
	}
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
		if !same && form != nil && known.index != nil && len(known.vars) == width {
			// Two reads whose indices are one linear form (`dom*K + t*2048
			// + i` spelled two ways by the two sides) read one element: one
			// block, rather than two tied by a consistency implication over
			// the index bits.
			if equalIndex, decided := indexRelation(form, known.index); decided && equalIndex {
				same = true
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
	bl.selects = append(bl.selects, selectAbstraction{span: span, idx: idx, vars: vars, index: index})
	return bl.varsBits(vars, width)
}

// consistency is the functional-consistency constraint over the element
// reads met so far (Ackermann's reduction): two reads of one span at equal
// indices hold equal values, and a read at an index equal to a constant
// holds that element parameter's value. Independent read values are sound
// for a proof — terms equal under independent values are equal under every
// memory — but a differing bit under independent values is a
// counterexample only where the values could come from one memory, so a
// difference counts only under this constraint. Quadratic in the reads of
// a span, each an equality over the 32 index bits; the node budget bounds
// it like everything else.
func (bl *blaster) consistency() int {
	cons := bddTrue
	if len(bl.selects) == 0 {
		return cons
	}
	equalBits := func(a, b []int) int {
		eq := bddTrue
		n := len(a)
		if len(b) < n {
			n = len(b)
		}
		for i := 0; i < n; i++ {
			eq = bl.apply(opAnd, eq, bl.not(bl.apply(opXor, a[i], b[i])))
			if bl.bdd.exceeded {
				return eq
			}
		}
		// A wider side's extra bits are zero: the values agree only when
		// those are zero too.
		for i := n; i < len(a); i++ {
			eq = bl.apply(opAnd, eq, bl.not(a[i]))
		}
		for i := n; i < len(b); i++ {
			eq = bl.apply(opAnd, eq, bl.not(b[i]))
		}
		return eq
	}
	constantBits := func(value uint64, width int) []int {
		out := make([]int, width)
		for i := range out {
			out[i] = bddFalse
			if (value>>uint(i))&1 == 1 {
				out[i] = bddTrue
			}
		}
		return out
	}
	implies := func(premise, conclusion int) {
		if premise == bddFalse {
			return
		}
		cons = bl.apply(opAnd, cons, bl.apply(opOr, bl.not(premise), conclusion))
	}
	// Two indices in linear normal form over the same unknowns are equal
	// or unequal by their constants alone (asm/effects.go indexRelation):
	// a pair provably at different elements — the arena's `base + 9`
	// against `base + 16` — needs no implication, which keeps the
	// constraint linear in the reads of such a body rather than quadratic.
	forms := make([]*linearForm, len(bl.selects))
	for k := range bl.selects {
		if bl.selects[k].index != nil {
			forms[k] = bl.selects[k].index.linearAt(32)
		}
	}
	for k := range bl.selects {
		a := bl.selects[k]
		formA := forms[k]
		aVal := bl.varsBits(a.vars, len(a.vars))
		for l := k + 1; l < len(bl.selects); l++ {
			b := bl.selects[l]
			if b.span != a.span {
				continue
			}
			if b.index != nil {
				if known, equal := indexRelation(formA, b.index); known && !equal {
					continue
				}
			}
			implies(equalBits(a.idx, b.idx), equalBits(aVal, bl.varsBits(b.vars, len(b.vars))))
			if bl.bdd.exceeded {
				return cons
			}
		}
		// The constant-index reads of the span are parameters (`v[3]`).
		for _, name := range bl.params {
			if rootParam(name) != a.span || len(name) <= len(a.span)+2 || name[len(a.span)] != '[' {
				continue
			}
			k, err := strconv.ParseInt(name[len(a.span)+1:len(name)-1], 10, 64)
			if err != nil || k < 0 {
				continue
			}
			if known, equal := indexRelation(formA, constTerm(uint64(k), 32)); known && !equal {
				continue
			}
			elem := bl.blast(paramTerm(name, bl.widths[name]))
			if elem == nil {
				continue
			}
			implies(equalBits(a.idx, constantBits(uint64(k), 32)), equalBits(aVal, elem))
			if bl.bdd.exceeded {
				return cons
			}
		}
	}
	return cons
}

func (bl *blaster) varsBits(vars []int, width int) []int {
	out := make([]int, width)
	for i := range out {
		if i < len(vars) {
			out[i] = bl.variable(vars[i])
		} else {
			out[i] = bddFalse
		}
	}
	return out
}

// blast returns width nodes (LSB first), or nil when the budget is exceeded.
func (bl *blaster) blast(t *term) []int {
	if bl.exceeded() {
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
		declared, known := bl.widths[t.name]
		if !known {
			// A parameter the decision was not told of would blast to a
			// constant zero and could turn a difference into a proof; the
			// diagram fails closed instead, as if over budget.
			bl.bdd.exceeded = true
			return nil
		}
		for i := 0; i < t.width; i++ {
			if i < declared {
				out[i] = bl.variable(bl.variableIndex(t.name, i))
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
		return bl.selectBits(t.name, idx, t.width, t.left)
	case termQuant:
		holds, ok := bl.quantify(t)
		if !ok {
			return nil
		}
		for i := range out {
			out[i] = bddFalse
		}
		out[0] = holds
		return out
	case termFloat:
		// An uninterpreted operation: its value is a fresh block shared by
		// every application of the same operation to the same operand
		// bits, and the consistency constraint ties applications whose
		// operands are equal (Ackermann's reduction over the operations,
		// Oak.Uninterpreted.ackermann_sound). The "span" is the operation
		// at its width; the "index" is the operands' bits in order. An
		// application over known operands folded when it was built
		// (floatTerm); the blaster folds nothing more, so the solver
		// written in Oak blasts the same terms to the same diagrams.
		var idx []int
		for _, arg := range []*term{t.left, t.right, t.cond} {
			if arg == nil {
				continue
			}
			bits := bl.blast(arg)
			if bits == nil {
				return nil
			}
			idx = append(idx, bits...)
		}
		return bl.selectBits(floatOpSpan(t.op, t.width), idx, t.width, nil)
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
		if cond == nil {
			return nil
		}
		if bl.assumed && bl.cnf == nil {
			if bl.bdd.apply(opAnd, bl.assume, bl.bdd.not(cond[0])) == bddFalse {
				bl.pruned++
				return bl.adapt(bl.blast(t.left), t.width) // the assumption implies the condition
			}
			if bl.bdd.apply(opAnd, bl.assume, cond[0]) == bddFalse {
				bl.pruned++
				return bl.adapt(bl.blast(t.right), t.width) // the assumption refutes it
			}
			if bl.bdd.exceeded {
				return nil
			}
		}
		left := bl.adapt(bl.blast(t.left), t.width)
		right := bl.adapt(bl.blast(t.right), t.width)
		if left == nil || right == nil {
			return nil
		}
		for i := range out {
			out[i] = bl.ite(cond[0], left[i], right[i])
		}
		if bl.exceeded() {
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
			out[i] = bl.apply(op, left[i], right[i])
		}
	case "add":
		out = bl.add(left, right, bddFalse)
	case "sub":
		negated := make([]int, len(right))
		for i := range right {
			negated[i] = bl.not(right[i])
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
			xor[i] = bl.apply(opXor, left[i], shifted[i])
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
	if bl.exceeded() {
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
		axb := bl.apply(opXor, a[i], b[i])
		out[i] = bl.apply(opXor, axb, carry)
		carry = bl.apply(opOr, bl.apply(opAnd, a[i], b[i]), bl.apply(opAnd, carry, axb))
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
	b := bl
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
			next[i] = bl.ite(count[s], shifted[i], current[i])
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
			partial[j] = bl.apply(opAnd, partial[j], b[i])
		}
		out = bl.add(out, partial, bddFalse)
		if bl.exceeded() {
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
			next[i] = bl.ite(count[s], rotated[i], current[i])
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
	b := bl
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
			next[i] = bl.ite(count[s], shifted[i], current[i])
		}
		current = next
	}
	return current
}

// counterexample turns a differing bit into a concrete parameter assignment.
func (bl *blaster) counterexample(x, y int) map[string]uint64 {
	return bl.counterexampleOf(bl.apply(opXor, x, y))
}

// counterexampleOf reads a parameter assignment off one satisfying path of
// a node.
func (bl *blaster) counterexampleOf(node int) map[string]uint64 {
	assignment := bl.bdd.satisfyingPath(node)
	env := make(map[string]uint64, len(bl.params))
	for variable, value := range assignment {
		owner, isParam := bl.owners[variable]
		if !value || !isParam {
			continue // select variables have no parameter to report
		}
		env[owner.param] |= uint64(1) << uint(owner.bit)
	}
	// The element reads the diagrams gave values to: each select at the
	// index its bits take under the assignment is the element parameter
	// `v[k]` with the value its variables take, so that evaluating the
	// terms on this input reads the memory the diagrams chose (an
	// uninterpreted operation's application, index nil, is not reported:
	// the evaluation computes the operation itself, which is what tells a
	// difference under the abstraction from a counterexample).
	for _, sel := range bl.selects {
		if sel.index == nil {
			continue
		}
		var k uint64
		for i, bit := range sel.idx {
			if bl.bdd.holdsUnder(bit, assignment) {
				k |= uint64(1) << uint(i)
			}
		}
		name := spanElemName(sel.span, int64(k))
		if _, given := env[name]; given {
			continue // a constant-index read of the same element: a parameter already reported
		}
		var value uint64
		for i, variable := range sel.vars {
			if assignment[variable] {
				value |= uint64(1) << uint(i)
			}
		}
		env[name] = value
	}
	return env
}

// quantify eliminates a quantifier's bound parameter from its body's
// diagram (docs/spec/10-syntax.md section 3e): `forall` is the
// conjunction and `exists` the disjunction of the two cofactors at each
// of the parameter's variables, bit 0 first — the diagram of the body
// with the variables gone, sound by Shannon's expansion. The clause
// engine has no cofactor and declines, as its twin written in Oak does
// (prove/solver/bdd.oak blast_term): the certificate rung leaves a
// quantified theorem to the diagrams.
func (bl *blaster) quantify(t *term) (int, bool) {
	op := opAnd
	if t.op == "exists" {
		op = opOr
	}
	width := int(t.value)
	if bl.cnf != nil {
		return 0, false
	}
	body := bl.blast(t.left)
	if body == nil {
		return 0, false
	}
	f := body[0]
	for bit := 0; bit < width; bit++ {
		v := bl.variableIndex(t.name, bit)
		f = bl.bdd.apply(op, bl.bdd.restrict(f, v, false), bl.bdd.restrict(f, v, true))
		if bl.exceeded() {
			return 0, false
		}
	}
	return f, true
}
