package asm

import (
	"fmt"
	"math/bits"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// The vector file of the verifier (docs/spec/94-assembler.md §8, the
// vector increment): a NEON register is a 128-bit value held as lanes of
// one width, each lane a term of the scalar language, so the lane-wise
// instructions the native backend emits (nativegen/simd.go) are lane
// functions over the same terms the scalar instructions produce, and a
// vector-valued result or parameter is its lanes. The lane functions are
// the ones docs/spec/93-simd.md and spec/lean/Oak/Simd.lean give the
// portable operations, so the Oak side (asm/verify_simd.go) and the
// machine side meet on identical constructors — the equality the decider
// then settles is between the instruction sequence and the operation
// sequence, not between two spellings of one lane function.

// vecValue is a 128-bit vector register as lanes of bits bits each, lane
// 0 the least significant (the lowest address when stored). The lane
// width is whatever the last writer used; a reader at another width
// repacks through the two 64-bit halves.
type vecValue struct {
	bits  int
	lanes []*term
}

// vecBits is the register's size in bits.
const vecBits = 128

// lanesAt views the value as lanes of the given width.
func (v vecValue) lanesAt(bits int) []*term {
	if v.bits == bits {
		return v.lanes
	}
	halves := v.lanes
	if v.bits != 64 {
		halves = packLanes(v.lanes, v.bits)
	}
	if bits == 64 {
		return halves
	}
	out := make([]*term, vecBits/bits)
	for k := range out {
		half := halves[(k*bits)/64]
		shift := (k * bits) % 64
		if lane, isPacked := unpackLane(half, shift, bits); isPacked {
			out[k] = lane // the lane a pack placed here, as it was
			continue
		}
		t := half
		if shift > 0 {
			t = binaryTerm("shr", half, constTerm(uint64(shift), 64))
		}
		out[k] = narrowLane(t, bits)
	}
	return out
}

// bitwiseLaneBits is the lane width a bitwise operation over two vectors
// is computed at: the finer of the operands' representations, and for two
// word-represented operands (reloaded from the frame, or a loop's fresh
// symbols) the finest width at which both words are recognizable packs —
// so the operation is spelled lane by lane, as the Oak side spells it,
// and a stored-and-reloaded vector meets the same terms as one kept in a
// register. Two words neither of which is a pack stay whole.
func bitwiseLaneBits(left, right vecValue) int {
	if bits := min(left.bits, right.bits); bits < 64 {
		return bits
	}
	for _, bits := range []int{8, 16, 32} {
		if packedAt(left, bits) && packedAt(right, bits) {
			return bits
		}
	}
	// Two words that are packs of nothing recognizable — a loop's fresh
	// symbols for two registers — are combined byte by byte: bitwise
	// operations distribute over lanes, and once a substitution makes the
	// words packs of Oak lanes the bytes are those lanes.
	return 8
}

// packedAt reports whether both words of a value are packs of lanes of
// the given width (a constant word is).
func packedAt(v vecValue, bits int) bool {
	for _, half := range v.halves() {
		if half.kind == termConst {
			continue
		}
		if !unpackWord(half, bits, map[int]*term{}) {
			return false
		}
	}
	return true
}

// extractedLane recognizes a lane extraction from a pack — `(word >> s) &
// mask(bits)` or `word & mask(bits)` where the word is a recognizable
// pack — and returns the lane placed there (a loop-carried register's
// fresh symbol, once substituted by the pack of its Oak lanes, yields
// those lanes rather than shifted masks over the pack).
func extractedLane(t *term) (*term, bool) {
	if t.kind != termBinary || t.op != "and" || t.right.kind != termConst || !isLowMask(t.right.value) || t.right.value == 0 {
		return nil, false
	}
	bits := bits.Len64(t.right.value)
	if bits == 0 || 64%bits != 0 {
		return nil, false
	}
	word, shift := t.left, 0
	if word.kind == termBinary && word.op == "shr" && word.right.kind == termConst {
		shift = int(word.right.value)
		word = word.left
	}
	if shift%bits != 0 || shift >= 64 || word.width != 64 {
		return nil, false
	}
	lane, ok := unpackLane(word, shift, bits)
	if !ok {
		return nil, false
	}
	return adaptWidth(lane, t.width), true
}

// unpackLane finds, in a 64-bit word packLanes built, the lane of the
// given width placed at the given shift, and returns the lane term itself
// (its masks and placement stripped). A vector stored to the frame and
// reloaded, or a loop-carried register expressed as the pack of its lanes,
// thereby yields the very lane terms it was packed from, so both sides
// of a comparison keep one spelling for one lane and decide as the same
// term where a diagram of the lanes would be beyond the budget.
func unpackLane(word *term, shift, bits int) (*term, bool) {
	lanes := map[int]*term{}
	if !unpackWord(word, bits, lanes) {
		return nil, false
	}
	if lane, placed := lanes[shift]; placed {
		return lane, true
	}
	return constTerm(0, bits), true // a position the pack left empty
}

// unpackWord decomposes a word into the lanes packLanes placed in it — an
// or of lanes each shifted to a distinct position, or a single placed lane
// — into lanes by shift; false when the word is not such a pack (an or of
// two vectors' words, say, whose lanes overlap).
func unpackWord(word *term, bits int, lanes map[int]*term) bool {
	if word.kind == termConst && word.value == 0 {
		return true
	}
	if word.kind != termBinary {
		return false
	}
	switch word.op {
	case "or":
		return unpackWord(word.left, bits, lanes) && unpackWord(word.right, bits, lanes)
	case "shl":
		if word.right.kind != termConst || word.right.value%uint64(bits) != 0 || word.right.value >= 64 {
			return false
		}
		return placeLane(word.left, int(word.right.value), bits, lanes)
	case "and":
		return placeLane(word, 0, bits, lanes)
	}
	return false
}

// placeLane records the lane placed at shift, refusing a position taken.
func placeLane(placed *term, shift, bits int, lanes map[int]*term) bool {
	lane, ok := placedLane(placed, bits)
	if !ok {
		return false
	}
	if _, taken := lanes[shift]; taken {
		return false
	}
	lanes[shift] = lane
	return true
}

// placedLane recognizes widenLane's placement of a lane at bit 0 of a
// 64-bit word — the lane zero-extended and masked to its width — and
// returns the lane at its width.
func placedLane(t *term, bits int) (*term, bool) {
	if t.kind == termConst {
		if t.value>>uint(bits) != 0 {
			return nil, false
		}
		return constTerm(t.value, bits), true
	}
	if t.kind != termBinary || t.op != "and" || t.right.kind != termConst || t.right.value != mask(bits) || t.width != 64 {
		return nil, false
	}
	inner := t.left
	switch inner.kind {
	case termParam:
		return &term{kind: termParam, width: bits, name: inner.name}, true // zeroExtend re-widthed the parameter
	case termCmp:
		return &term{kind: termCmp, width: bits, op: inner.op, left: inner.left, right: inner.right}, true
	case termBinary:
		// zeroExtend of a computation: `and(lane, mask(lane.width))` at 64.
		if inner.op == "and" && inner.right.kind == termConst && inner.right.value == mask(bits) && inner.left.width == bits {
			return inner.left, true
		}
	}
	return nil, false
}

// narrowLane views a term at a lane width with an explicit mask. Unlike
// truncate, it does not take a parameter to be bounded by the narrower
// width: a 64-bit input read as bytes (dup, a d-view store, the lanes of a
// half) keeps only its low bits, as the machine does.
func narrowLane(t *term, bits int) *term {
	if t.width == bits {
		return t
	}
	switch t.kind {
	case termConst:
		return constTerm(t.value, bits)
	case termCmp:
		return truncate(t, bits) // a 1/0 value at any width
	case termBinary:
		// A lane already masked to its width (widenLane's placement) needs
		// no second mask.
		if t.op == "and" && t.right.kind == termConst && t.right.value == mask(bits) && t.left.width == bits {
			return t.left
		}
		if t.op == "and" && t.right.kind == termConst && t.right.value == mask(bits) {
			return &term{kind: termBinary, width: bits, op: "and", left: t.left, right: constTerm(mask(bits), bits)}
		}
	}
	return &term{kind: termBinary, width: bits, op: "and", left: t, right: constTerm(mask(bits), bits)}
}

// widenLane places a lane's bits in a wider term: the lane masked to its
// width (a parameter node narrowed from a wider declaration keeps only
// those bits), then zero-extended.
func widenLane(t *term, bits, width int) *term {
	if t.kind == termConst {
		return constTerm(t.value&mask(bits), width)
	}
	return binaryTerm("and", zeroExtend(t, width), constTerm(mask(bits), width))
}

// halves is the value as its low and high 64-bit words.
func (v vecValue) halves() []*term { return v.lanesAt(64) }

// packLanes assembles lanes of bits bits into the two 64-bit halves.
func packLanes(lanes []*term, bits int) []*term {
	halves := []*term{constTerm(0, 64), constTerm(0, 64)}
	for k, lane := range lanes {
		position := k * bits
		if position >= vecBits {
			break
		}
		placed := widenLane(lane, bits, 64)
		if shift := position % 64; shift > 0 {
			placed = binaryTerm("shl", placed, constTerm(uint64(shift), 64))
		}
		half := position / 64
		if halves[half].kind == termConst && halves[half].value == 0 {
			halves[half] = placed
		} else {
			halves[half] = binaryTerm("or", halves[half], placed)
		}
	}
	return halves
}

// vecOfLanes is a value from a full set of lanes.
func vecOfLanes(lanes []*term, bits int) vecValue { return vecValue{bits: bits, lanes: lanes} }

// vecFromLow is a value whose low bits are the term (a scalar view write:
// the rest of the register is zeroed).
func vecFromLow(t *term) vecValue {
	return vecValue{bits: 64, lanes: []*term{widenLane(t, min(t.width, 64), 64), constTerm(0, 64)}}
}

// vecZero is the zero vector.
func vecZero() vecValue {
	return vecValue{bits: 64, lanes: []*term{constTerm(0, 64), constTerm(0, 64)}}
}

// readVec reads a vector register whole. A callee-saved vector register
// (v8–v15) read before any write carries the caller's value: an opaque
// symbol per half, which the prologue's save and the epilogue's restore
// round-trip.
func (s *symbolicState) readVec(num int) (vecValue, bool) {
	if value, bound := s.vregs[num]; bound {
		return value, true
	}
	if s.arch != ArchRV64 && calleeSavedVector(num) {
		// AAPCS64 preserves the low halves of v8–v15; the RVV psABI
		// preserves no vector register, so on RV64 an unwritten one is unbound.
		value := vecValue{bits: 64, lanes: []*term{paramTerm(fmt.Sprintf("entry.v%d.lo", num), 64), paramTerm(fmt.Sprintf("entry.v%d.hi", num), 64)}}
		s.writeVec(num, value)
		return value, true
	}
	return vecValue{}, false
}

// writeVec binds a vector register whole.
func (s *symbolicState) writeVec(num int, value vecValue) {
	if s.vregs == nil {
		s.vregs = map[int]vecValue{}
	}
	s.vregs[num] = value
}

// readVecView reads a register through a view: an arrangement gives the
// lanes at the arrangement's width (a 64-bit arrangement the low ones), a
// scalar view the low lane at its width, a lane reference that lane.
func (s *symbolicState) readVecView(reg Register) (*term, bool) {
	value, ok := s.readVec(reg.Num)
	if !ok {
		return nil, false
	}
	bits := 8 * laneBytes(reg.Vec)
	if bits == 0 || bits > 64 {
		return nil, false
	}
	lanes := value.lanesAt(bits)
	lane := 0
	if reg.Lane >= 0 {
		lane = reg.Lane
	}
	if lane >= len(lanes) {
		return nil, false
	}
	return lanes[lane], true
}

// arrangementLanes is the lane count and lane width of a vector
// arrangement ("16b" → 16 lanes of 8 bits; "8b" → 8 of 8, the low half).
func arrangementLanes(arr string) (count, bits int, ok bool) {
	count, isArrangement := vectorArrangements[arr]
	if !isArrangement {
		return 0, 0, false
	}
	return count, 8 * laneBytes(arr), true
}

// laneOperands reads the lanes of a vector operand at an arrangement,
// requiring the operand to be spelled with that arrangement.
func (s *symbolicState) laneOperands(reg Register, arr string) ([]*term, bool) {
	if reg.Class != ClassV || reg.Vec != arr || reg.Lane >= 0 {
		return nil, false
	}
	count, bits, ok := arrangementLanes(arr)
	if !ok {
		return nil, false
	}
	value, bound := s.readVec(reg.Num)
	if !bound {
		return nil, false
	}
	return value.lanesAt(bits)[:count], true
}

// writeLanes writes lanes at an arrangement; a 64-bit arrangement zeroes
// the high half, as the machine does.
func (s *symbolicState) writeLanes(reg Register, lanes []*term, bits int) {
	full := vecBits / bits
	for len(lanes) < full {
		lanes = append(lanes, constTerm(0, bits))
	}
	s.writeVec(reg.Num, vecOfLanes(lanes[:full], bits))
}

// hasVectorOperand reports an instruction touching the vector file.
func hasVectorOperand(instr Instruction) bool {
	for _, reg := range registerOperands(instr.Operands) {
		if reg.Class == ClassV {
			return true
		}
	}
	return false
}

// --- the lane functions -------------------------------------------------
//
// Each is a lane of one NEON instruction and, by the same definition, of
// one Oak.Simd operation; both sides of the verifier build lanes with
// these (the Lean statement of the correspondence is Oak.NeonSemantics).

func laneAllOnes(bits int) *term { return constTerm(mask(bits), bits) }

// laneBinary applies an integer lane operation.
func laneBinary(op string, x, y *term) *term {
	bits := x.width
	switch op {
	case "add", "sub", "and", "or", "xor":
		return binaryTerm(op, x, y)
	case "umin":
		return iteTerm(cmpTerm("lo", x, y), x, y)
	case "umax":
		return iteTerm(cmpTerm("hi", x, y), x, y)
	case "uqsub":
		// Saturating subtract: x - y when y < x, else 0 (Oak.Simd.subSat).
		return iteTerm(cmpTerm("hi", x, y), binaryTerm("sub", x, y), constTerm(0, bits))
	case "uqadd":
		sum := binaryTerm("add", x, y)
		return iteTerm(cmpTerm("lo", sum, x), laneAllOnes(bits), sum)
	case "cmeq":
		return iteTerm(cmpTerm("eq", x, y), laneAllOnes(bits), constTerm(0, bits))
	case "cmhi":
		return iteTerm(cmpTerm("hi", x, y), laneAllOnes(bits), constTerm(0, bits))
	case "cmhs":
		return iteTerm(cmpTerm("hs", x, y), laneAllOnes(bits), constTerm(0, bits))
	}
	return nil
}

// laneShift shifts a lane by a constant count below the lane width.
func laneShift(op string, x *term, count int64) *term {
	return binaryTerm(op, x, constTerm(uint64(count), x.width))
}

// laneTable is the byte-table lookup: lane index into table, 0 for an
// index at or beyond the table (Oak.Simd.tbl, NEON's tbl rule).
func laneTable(table []*term, index *term) *term {
	out := constTerm(0, index.width)
	for k := len(table) - 1; k >= 0; k-- {
		out = iteTerm(cmpTerm("eq", index, constTerm(uint64(k), index.width)), table[k], out)
	}
	return out
}

// laneExtract is ext: the sixteen bytes of low ++ high starting at position.
func laneExtract(low, high []*term, position int) []*term {
	joined := append(append([]*term{}, low...), high...)
	return joined[position : position+len(low)]
}

// laneReduce folds the lanes: the unsigned maximum, minimum, or the
// wrapping sum.
func laneReduce(op string, lanes []*term) *term {
	acc := lanes[0]
	for _, lane := range lanes[1:] {
		switch op {
		case "umaxv":
			acc = iteTerm(cmpTerm("hi", lane, acc), lane, acc)
		case "uminv":
			acc = iteTerm(cmpTerm("lo", lane, acc), lane, acc)
		case "addv":
			acc = binaryTerm("add", acc, lane)
		}
	}
	return acc
}

// laneMovemask packs the top bit of each lane into bit k of a 32-bit
// scalar (Oak.Simd.movemask).
func laneMovemask(lanes []*term) *term {
	out := constTerm(0, 32)
	for k, lane := range lanes {
		top := zeroExtend(truncate(binaryTerm("shr", lane, constTerm(uint64(lane.width-1), lane.width)), 1), 32)
		if k > 0 {
			top = binaryTerm("shl", top, constTerm(uint64(k), 32))
		}
		out = binaryTerm("or", out, top)
	}
	return out
}

// laneAny / laneAll: some lane nonzero, every lane nonzero, as 1-bit terms.
func laneAny(lanes []*term) *term {
	out := constTerm(0, 1)
	for _, lane := range lanes {
		out = binaryTerm("or", out, cmpTerm("ne", lane, constTerm(0, lane.width)))
	}
	return out
}

func laneAll(lanes []*term) *term {
	out := constTerm(1, 1)
	for _, lane := range lanes {
		out = binaryTerm("and", out, truncate(cmpTerm("ne", lane, constTerm(0, lane.width)), 1))
	}
	return out
}

// --- the instructions ------------------------------------------------------

// stepVector executes one instruction with a vector operand: the NEON
// subset the native backend emits, each as its lane function.
func (x *pathExecutor) stepVector(instr Instruction, state *symbolicState) (string, bool) {
	refuse := func() (string, bool) {
		return "a floating-point or vector instruction (" + instr.Mnemonic + ")", false
	}
	if handled, reason, ok := x.stepFloat(instr, state); handled {
		return reason, ok
	}
	ops := instr.Operands
	reg := func(i int) (Register, bool) {
		if i >= len(ops) {
			return Register{}, false
		}
		r, ok := ops[i].(Register)
		return r, ok
	}
	imm := func(i int) (int64, bool) {
		if i >= len(ops) {
			return 0, false
		}
		v, ok := ops[i].(Immediate)
		return v.Value << uint(v.Shift), ok
	}
	switch instr.Mnemonic {
	case "orr", "and", "eor", "bic", "mov":
		// Bitwise over the whole register (any arrangement, spelled 16b by
		// the backend); orr vD, vN, vN and mov are the vector move.
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || d.Class != ClassV || n.Class != ClassV || d.Lane >= 0 || n.Lane >= 0 {
			return refuse()
		}
		m := n
		if instr.Mnemonic != "mov" {
			var okM bool
			if m, okM = reg(2); !okM || m.Class != ClassV || m.Lane >= 0 {
				return refuse()
			}
		}
		left, okL := state.readVec(n.Num)
		right, okR := state.readVec(m.Num)
		if !okL || !okR {
			return "unbound vector register read", false
		}
		if instr.Mnemonic == "mov" || (n.Num == m.Num && (instr.Mnemonic == "orr" || instr.Mnemonic == "and")) {
			// The vector move: orr/and of a register with itself. eor and
			// bic of a register with itself are zero, not a move — the
			// backend spells `xor(v, v)` as `eor vD, vN, vN` once it reads
			// v in place — so they fall through to the lane-wise operation.
			state.writeVec(d.Num, left)
			return "", true
		}
		op := map[string]string{"orr": "or", "and": "and", "eor": "xor", "bic": "and"}[instr.Mnemonic]
		bits := bitwiseLaneBits(left, right)
		l, r := left.lanesAt(bits), right.lanesAt(bits)
		out := make([]*term, len(l))
		for k := range l {
			rk := r[k]
			if instr.Mnemonic == "bic" {
				rk = binaryTerm("xor", rk, laneAllOnes(bits))
			}
			out[k] = binaryTerm(op, l[k], rk)
		}
		state.writeVec(d.Num, vecOfLanes(out, bits))
		return "", true
	case "add", "sub", "umin", "umax", "uqsub", "uqadd", "cmeq", "cmhi", "cmhs":
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || d.Class != ClassV || d.Vec != n.Vec {
			return refuse()
		}
		count, bits, ok := arrangementLanes(d.Vec)
		if !ok {
			return refuse()
		}
		left, okL := state.laneOperands(n, d.Vec)
		if !okL {
			return "unbound vector register read", false
		}
		var right []*term
		if zero, isImm := imm(2); isImm {
			if zero != 0 || instr.Mnemonic != "cmeq" {
				return refuse()
			}
			right = make([]*term, count)
			for k := range right {
				right[k] = constTerm(0, bits)
			}
		} else {
			m, okM := reg(2)
			if !okM {
				return refuse()
			}
			right, okM = state.laneOperands(m, d.Vec)
			if !okM {
				return "unbound vector register read", false
			}
		}
		out := make([]*term, count)
		for k := range out {
			out[k] = laneBinary(instr.Mnemonic, left[k], right[k])
		}
		state.writeLanes(d, out, bits)
		return "", true
	case "ushr", "sshr", "shl":
		d, okD := reg(0)
		n, okN := reg(1)
		count, isImm := imm(2)
		if !okD || !okN || !isImm || d.Class != ClassV || d.Vec != n.Vec {
			return refuse()
		}
		_, bits, ok := arrangementLanes(d.Vec)
		if !ok || count < 0 || count >= int64(bits) {
			return refuse()
		}
		lanes, okL := state.laneOperands(n, d.Vec)
		if !okL {
			return "unbound vector register read", false
		}
		op := map[string]string{"ushr": "shr", "sshr": "sar", "shl": "shl"}[instr.Mnemonic]
		out := make([]*term, len(lanes))
		for k := range out {
			out[k] = laneShift(op, lanes[k], count)
		}
		state.writeLanes(d, out, bits)
		return "", true
	case "dup":
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || d.Class != ClassV {
			return refuse()
		}
		count, bits, ok := arrangementLanes(d.Vec)
		if !ok {
			return refuse()
		}
		var lane *term
		switch {
		case n.Class == ClassW || n.Class == ClassX:
			value, okR := state.read(n)
			if !okR {
				return "unbound register read", false
			}
			lane = narrowLane(value, bits)
		case n.Class == ClassV && n.Lane >= 0 && 8*laneBytes(n.Vec) == bits:
			var okR bool
			if lane, okR = state.readVecView(n); !okR {
				return "unbound vector register read", false
			}
		default:
			return refuse()
		}
		out := make([]*term, count)
		for k := range out {
			out[k] = lane
		}
		state.writeLanes(d, out, bits)
		return "", true
	case "movi":
		d, okD := reg(0)
		value, isImm := imm(1)
		if !okD || !isImm || d.Class != ClassV || len(ops) != 2 {
			return refuse()
		}
		count, bits, ok := arrangementLanes(d.Vec)
		if !ok {
			return refuse()
		}
		out := make([]*term, count)
		for k := range out {
			out[k] = constTerm(uint64(value), bits)
		}
		state.writeLanes(d, out, bits)
		return "", true
	case "tbl":
		// tbl vD.16b, {vT.16b}, vI.16b: one table register.
		d, okD := reg(0)
		if !okD || d.Class != ClassV || d.Vec != "16b" || len(ops) != 3 {
			return refuse()
		}
		list, isList := ops[1].(RegisterList)
		i, okI := reg(2)
		if !isList || len(list.Regs) != 1 || !okI {
			return refuse()
		}
		table, okT := state.laneOperands(list.Regs[0], "16b")
		index, okX := state.laneOperands(i, "16b")
		if !okT || !okX {
			return "unbound vector register read", false
		}
		out := make([]*term, 16)
		for k := range out {
			out[k] = laneTable(table, index[k])
		}
		state.writeLanes(d, out, 8)
		return "", true
	case "ext":
		d, okD := reg(0)
		n, okN := reg(1)
		m, okM := reg(2)
		position, isImm := imm(3)
		if !okD || !okN || !okM || !isImm || d.Class != ClassV || d.Vec != "16b" || position < 0 || position > 15 {
			return refuse()
		}
		low, okL := state.laneOperands(n, "16b")
		high, okH := state.laneOperands(m, "16b")
		if !okL || !okH {
			return "unbound vector register read", false
		}
		state.writeLanes(d, laneExtract(low, high, int(position)), 8)
		return "", true
	case "umaxv", "uminv", "addv":
		// A reduction into a scalar view: the rest of the register zeroed.
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || d.Class != ClassV || d.Lane >= 0 || n.Class != ClassV {
			return refuse()
		}
		_, bits, ok := arrangementLanes(n.Vec)
		if !ok || 8*laneBytes(d.Vec) != bits || len(d.Vec) != 1 {
			return refuse()
		}
		lanes, okL := state.laneOperands(n, n.Vec)
		if !okL {
			return "unbound vector register read", false
		}
		state.writeVec(d.Num, vecFromLow(laneReduce(instr.Mnemonic, lanes)))
		return "", true
	case "cnt":
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || d.Class != ClassV || d.Vec != n.Vec || (d.Vec != "8b" && d.Vec != "16b") {
			return refuse()
		}
		lanes, okL := state.laneOperands(n, d.Vec)
		if !okL {
			return "unbound vector register read", false
		}
		out := make([]*term, len(lanes))
		for k := range out {
			out[k] = binaryTerm("cnt", lanes[k], constTerm(0, 8))
		}
		state.writeLanes(d, out, 8)
		return "", true
	case "umov", "smov":
		// umov wD, vN.b[k]: the lane into the general register.
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN || (d.Class != ClassW && d.Class != ClassX) || n.Class != ClassV || n.Lane < 0 {
			return refuse()
		}
		lane, ok := state.readVecView(n)
		if !ok {
			return "unbound vector register read", false
		}
		if instr.Mnemonic == "smov" {
			state.write(d, extendTerm(lane, lane.width, widthOf(d.Class), true))
		} else {
			state.write(d, zeroExtend(lane, widthOf(d.Class)))
		}
		return "", true
	case "fmov":
		// The bit moves between the files: fmov dD, xN / sD, wN and back.
		d, okD := reg(0)
		n, okN := reg(1)
		if !okD || !okN {
			return refuse()
		}
		switch {
		case d.Class == ClassV && (n.Class == ClassW || n.Class == ClassX) && d.Lane < 0 && (d.Vec == "d" || d.Vec == "s"):
			value, ok := state.read(n)
			if !ok {
				return "unbound register read", false
			}
			state.writeVec(d.Num, vecFromLow(narrowLane(value, 8*laneBytes(d.Vec))))
			return "", true
		case (d.Class == ClassW || d.Class == ClassX) && n.Class == ClassV && n.Lane < 0 && (n.Vec == "d" || n.Vec == "s"):
			lane, ok := state.readVecView(n)
			if !ok {
				return "unbound vector register read", false
			}
			state.write(d, zeroExtend(lane, widthOf(d.Class)))
			return "", true
		}
		return refuse()
	}
	return refuse()
}

// vectorFrameAccessAt executes a load or store of vector registers at an
// entry-relative frame address: a q view is two 8-byte slots (the low half
// at the lower address), a d or s view its low bits. A load through a
// narrower view zeroes the rest of the register.
func (x *pathExecutor) vectorFrameAccessAt(instr Instruction, state *symbolicState, addr int64, regs []Register) (string, bool) {
	if !isStoreMnemonic(instr.Mnemonic) && !isPlainLoad(instr.Mnemonic) && instr.Mnemonic != "ldp" {
		return "a vector frame access outside the modeled subset (" + instr.Mnemonic + ")", false
	}
	if state.frame == nil {
		state.frame = map[int64]frameSlot{}
	}
	offset := addr
	for _, reg := range regs {
		if reg.Class != ClassV || reg.Lane >= 0 {
			return "a vector frame access with a mixed register list", false
		}
		size := reg.VecBytes()
		if size != 16 && size != 8 && size != 4 {
			return "a vector frame access through the " + reg.Vec + " view", false
		}
		if isStoreMnemonic(instr.Mnemonic) {
			value, ok := state.readVec(reg.Num)
			if !ok {
				return "unbound vector register read", false
			}
			halves := value.halves()
			if size == 16 {
				state.storeSlot(offset, halves[0], 8)
				state.storeSlot(offset+8, halves[1], 8)
				whole := value
				low := state.frame[offset]
				low.vec, low.hi = &whole, halves[1]
				state.frame[offset] = low
			} else {
				state.storeSlot(offset, narrowLane(halves[0], int(size)*8), size)
			}
		} else {
			slot := func(at, width int64) (*term, bool) {
				if value, ok := state.loadSlot(at, width); ok {
					return value, true
				}
				return state.opaqueSlot(at, width)
			}
			if size == 16 {
				// A whole vector stored here and untouched since: the same
				// value, lane for lane, rather than its two halves.
				if lowSlot, ok := state.frame[offset]; ok && lowSlot.vec != nil && lowSlot.width == 8 {
					if highSlot, okH := state.frame[offset+8]; okH && highSlot.width == 8 && highSlot.value == lowSlot.hi {
						state.writeVec(reg.Num, *lowSlot.vec)
						offset += size
						continue
					}
				}
				low, okL := slot(offset, 8)
				high, okH := slot(offset+8, 8)
				if !okL || !okH {
					return "a load from a frame slot never stored on this path", false
				}
				state.writeVec(reg.Num, vecOfLanes([]*term{low, high}, 64))
			} else {
				value, ok := slot(offset, size)
				if !ok {
					return "a load from a frame slot never stored on this path", false
				}
				state.writeVec(reg.Num, vecFromLow(value))
			}
		}
		offset += size
	}
	return "", true
}

// loadVector executes `ldr qD, [xB, wI, uxtw #s]` / `ldr qD, [xB, #off]`
// through a span base: the sixteen bytes from element wI (the seam checker
// has placed the access under a guard proving wI + 16/elem <= len), one
// element term per lane. A d view reads eight bytes into the low half; an
// s view one four-byte element — an f32 span's element into the low lane,
// the rest of the register zero as every scalar write leaves it
// (docs/spec/94-assembler.md §8, floats in loop bodies).
func (x *pathExecutor) loadVector(instr Instruction, state *symbolicState) (string, bool) {
	dest := instr.Operands[0].(Register)
	mem, isMem := instr.Operands[1].(Memory)
	if !isMem || instr.Mnemonic != "ldr" || dest.Lane >= 0 {
		return "a vector load outside the modeled subset (" + instr.Mnemonic + ")", false
	}
	size := dest.VecBytes()
	if size != 16 && size != 8 && size != 4 {
		return "a vector load through the " + dest.Vec + " view", false
	}
	if mem.Base.Class == ClassSP {
		return "frame memory", false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return "a vector load through a register that is not a span base", false
	}
	param, baseOffset, isSpan := spanBaseOf(base)
	if !isSpan {
		return "a vector load through a register that is not a span base", false
	}
	elem, known := x.spans[param]
	if !known || elem == 0 || elem > size || baseOffset%elem != 0 || mem.Mode != MemOffset {
		return "a vector load over a base that is not a span of whole elements", false
	}
	var index *term
	if mem.Index != nil {
		if int64(1)<<uint(mem.Shift) != elem {
			return "an indexed vector load whose scale is not the element size", false
		}
		value, ok := state.read(*mem.Index)
		if !ok {
			return "unbound register read", false
		}
		index = truncate(value, 32)
		if extra := baseOffset / elem; extra != 0 {
			index = binaryTerm("add", index, constTerm(uint64(extra), 32))
		}
	} else {
		if mem.Offset < 0 || mem.Offset%elem != 0 {
			return "a vector load not aligned to an element", false
		}
		index = constTerm(uint64(mem.Offset/elem+baseOffset/elem), 32)
	}
	bits := int(elem) * 8
	lanes := make([]*term, size/elem)
	for k := range lanes {
		at := index
		if k > 0 {
			at = binaryTerm("add", index, constTerm(uint64(k), 32))
		}
		lanes[k] = x.elementIn(state, param, at, bits)
	}
	state.writeLanes(dest, lanes, bits)
	return "", true
}

// --- the contract ----------------------------------------------------------

// vectorShape resolves a `simd.<Name>` type to its integer lane shape
// (the float vectors are outside the subset).
func vectorShape(expr ast.Expression) (typechecker.SimdShape, bool) {
	name := typeText(expr)
	if !strings.HasPrefix(name, "simd.") {
		return typechecker.SimdShape{}, false
	}
	for _, shape := range typechecker.SimdShapes {
		if shape.TypeName == name[len("simd."):] {
			return shape, true
		}
	}
	return typechecker.SimdShape{}, false
}

// laneWidth is a shape's lane width in bits.
func laneWidth(shape typechecker.SimdShape) int { return vecBits / shape.Lanes }

// vectorParamValue is a vector parameter as its lane leaves `name[k]`
// (the Oak side names them the same way, paramAggregate over the lane
// array), bound whole into the register the contract assigns.
func vectorParamValue(name string, shape typechecker.SimdShape, input func(name string, width int) *term) vecValue {
	bits := laneWidth(shape)
	lanes := make([]*term, shape.Lanes)
	for k := range lanes {
		lanes[k] = input(spanElemName(name, int64(k)), bits)
	}
	return vecOfLanes(lanes, bits)
}

// verifyVectorResult verifies a function whose result is a vector: the
// executor delivers v0 one 64-bit half at a time, the Oak body lowers to
// its lanes (asm/verify_simd.go) packed the same way, and each half is
// decided as a scalar equality. Data-dependent loops on either side stay
// trusted for vector results (the loop machinery couples scalars).
func verifyVectorResult(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, shape typechecker.SimdShape) Verdict {
	trusted := func(reason string) Verdict {
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (%s) — trusted per docs/spec/94-assembler.md §5", fn.Name, reason)}
	}
	lowering := prepareLowering(fn, sig, nil)
	typ, ok := lowering.oakTypeOf(sig.ReturnType)
	if !ok {
		return trusted("a vector result type without a model")
	}
	value, reason, ok := lowering.aggregateValue(oakBody, typ)
	if !ok {
		return trusted("the Oak body contains " + reason)
	}
	if len(lowering.loops) > 0 {
		return trusted("a vector result through a data-dependent loop")
	}
	lanes := make([]*term, len(value.elems))
	for k, elem := range value.elems {
		lanes[k] = elem.scalar
		if shape.Float {
			lanes[k] = floatCanonicalNaN(narrowLane(elem.scalar, laneWidth(shape)), laneWidth(shape))
		}
	}
	oakHalves := packLanes(lanes, laneWidth(shape))
	var verdicts []Verdict
	for half := 0; half < 2; half++ {
		asmTerm, exec, reason, ok := executeBodyHalf(fn, sig, nil, half)
		if !ok {
			return trusted(reason)
		}
		if asmTerm == trapPath {
			return trusted("every path traps")
		}
		if len(exec.loops) > 0 {
			return trusted("a vector result through a data-dependent loop")
		}
		note := " (low half of the vector result)"
		if half == 1 {
			note = " (high half of the vector result)"
		}
		if shape.Float {
			// The machine's lanes up to their NaN payloads, as the Oak side's.
			bits := laneWidth(shape)
			machine := vecValue{bits: 64, lanes: []*term{asmTerm, constTerm(0, 64)}}.lanesAt(bits)[:vecBits/bits/2]
			for k := range machine {
				machine[k] = floatCanonicalNaN(machine[k], bits)
			}
			asmTerm = packLanes(machine, bits)[0]
		}
		verdict := decideEqual(fn, lowering, asmTerm, oakHalves[half], 64, note)
		if verdict.Kind == VerdictMismatch {
			return verdict
		}
		verdicts = append(verdicts, verdict)
	}
	if verdicts[0].Kind == VerdictProven && verdicts[1].Kind == VerdictProven {
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body at the bit level (128-bit vector result, both halves)", fn.Name)}
	}
	for _, verdict := range verdicts {
		if verdict.Kind == VerdictWitnessed {
			return verdict
		}
	}
	return verdicts[0]
}
