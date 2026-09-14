package asm

import "sync/atomic"

// A small reduced ordered binary decision diagram (ROBDD) for the §8
// verifier's bit-blaster (docs/spec/94-assembler.md). Nodes are canonical:
// two equal boolean functions are the same node index, so equivalence of
// two blasted terms is index equality per bit, and a differing bit yields a
// concrete counterexample by walking a path to the true terminal. A node
// budget keeps blow-up fail-closed: when exceeded, the caller keeps the
// labeled witness-checked verdict instead of claiming proof.

// Edges carry a complement bit: edge = 2*node + c, and the function of the
// complemented edge is the negation of the node's. One terminal node
// (index 0) stands for false, so zero-initialized lanes read as false as
// they always did, and true is the terminal's complement, edge 1.
// Negation is then a bit flip, and a function and its negation share
// every node. The canonical form keeps a node's high edge positive (mk
// normalizes), so two equal functions are still one edge — the equality
// test the decider relies on. The Oak solver (prove/solver/bdd.oak) is the
// same engine in Oak and must stay node-for-node its twin.
const (
	bddFalse = 0
	bddTrue  = 1
)

type bddNode struct {
	variable int // ordering position; terminals use bddTerminalVar
	low      int // cofactor for variable = 0
	high     int // cofactor for variable = 1
}

const bddTerminalVar = int(^uint(0) >> 1)

// The unique table and the operation cache are open-addressed hash tables
// over the node ids (docs/notes/formal-methods-performance-2026-09.md,
// item 2): flat slices of fixed-width entries, linear probing, a load
// factor of at most one half, growth by rehashing into twice the capacity.
// Node ids fit in 32 bits (the budget is two million). Go maps keyed by
// the same triples were the engine's measured cost — the diagrams are
// built and read through these two tables and almost nothing else.
type uniqueEntry struct{ variable, low, high, node int32 }
type opEntry struct{ op, a, b, result int32 }

type uniqueTable struct {
	entries []uniqueEntry // node < 0 marks an empty slot
	count   int
}

type opTable struct {
	entries []opEntry // result < 0 marks an empty slot
	count   int
}

func hashMix(a, b, c uint32) uint32 {
	h := a*0x9E3779B1 ^ b*0x85EBCA77 ^ c*0xC2B2AE3D
	h ^= h >> 15
	h *= 0x2C1B3C6D
	h ^= h >> 12
	return h
}

func newUniqueTable(capacity int) *uniqueTable {
	t := &uniqueTable{entries: make([]uniqueEntry, capacity)}
	for i := range t.entries {
		t.entries[i].node = -1
	}
	return t
}

func (t *uniqueTable) lookup(variable, low, high int32) (int32, bool) {
	mask := uint32(len(t.entries) - 1)
	for i := hashMix(uint32(variable), uint32(low), uint32(high)) & mask; ; i = (i + 1) & mask {
		e := &t.entries[i]
		if e.node < 0 {
			return 0, false
		}
		if e.variable == variable && e.low == low && e.high == high {
			return e.node, true
		}
	}
}

// insert adds a key known to be absent.
func (t *uniqueTable) insert(variable, low, high, node int32) {
	if 2*(t.count+1) > len(t.entries) {
		t.grow()
	}
	mask := uint32(len(t.entries) - 1)
	i := hashMix(uint32(variable), uint32(low), uint32(high)) & mask
	for t.entries[i].node >= 0 {
		i = (i + 1) & mask
	}
	t.entries[i] = uniqueEntry{variable, low, high, node}
	t.count++
}

func (t *uniqueTable) grow() {
	old := t.entries
	t.entries = make([]uniqueEntry, 2*len(old))
	for i := range t.entries {
		t.entries[i].node = -1
	}
	t.count = 0
	for _, e := range old {
		if e.node >= 0 {
			t.insert(e.variable, e.low, e.high, e.node)
		}
	}
}

func newOpTable(capacity int) *opTable {
	t := &opTable{entries: make([]opEntry, capacity)}
	for i := range t.entries {
		t.entries[i].result = -1
	}
	return t
}

func (t *opTable) lookup(op, a, b int32) (int32, bool) {
	mask := uint32(len(t.entries) - 1)
	for i := hashMix(uint32(op), uint32(a), uint32(b)) & mask; ; i = (i + 1) & mask {
		e := &t.entries[i]
		if e.result < 0 {
			return 0, false
		}
		if e.a == a && e.b == b && e.op == op {
			return e.result, true
		}
	}
}

// insert adds a key known to be absent.
func (t *opTable) insert(op, a, b, result int32) {
	if 2*(t.count+1) > len(t.entries) {
		t.grow()
	}
	mask := uint32(len(t.entries) - 1)
	i := hashMix(uint32(op), uint32(a), uint32(b)) & mask
	for t.entries[i].result >= 0 {
		i = (i + 1) & mask
	}
	t.entries[i] = opEntry{op, a, b, result}
	t.count++
}

func (t *opTable) grow() {
	old := t.entries
	t.entries = make([]opEntry, 2*len(old))
	for i := range t.entries {
		t.entries[i].result = -1
	}
	t.count = 0
	for _, e := range old {
		if e.result >= 0 {
			t.insert(e.op, e.a, e.b, e.result)
		}
	}
}

type bdd struct {
	nodes    []bddNode
	unique   *uniqueTable
	memo     *opTable
	budget   int
	exceeded bool
	// stop, when set, ends this diagram as if its budget were exceeded:
	// another variable order over the same terms has already decided.
	stop *atomic.Bool
}

const (
	opAnd = iota
	opOr
	opXor
)

func newBDD(budget int) *bdd {
	b := &bdd{unique: newUniqueTable(1 << 16), memo: newOpTable(1 << 16), budget: budget}
	b.nodes = []bddNode{{variable: bddTerminalVar}}
	return b
}

// variableOf is the variable of an edge's node; a terminal edge's is the
// terminal marker, which orders after every real variable.
func (b *bdd) variableOf(e int) int { return b.nodes[e>>1].variable }

// low and high are an edge's cofactors: the node's, complemented when the
// edge is (Oak.BddComplement.cofactor_complement).
func (b *bdd) low(e int) int  { return b.nodes[e>>1].low ^ (e & 1) }
func (b *bdd) high(e int) int { return b.nodes[e>>1].high ^ (e & 1) }

// mk returns the canonical edge for (variable, low, high). A complemented
// high edge is normalized by complementing both cofactors and the result
// (Oak.BddComplement.mk_complement), so every node's high edge is
// positive and equal functions are one edge.
func (b *bdd) mk(variable, low, high int) int {
	if low == high {
		return low
	}
	flip := high & 1
	low, high = low^flip, high^flip
	if n, ok := b.unique.lookup(int32(variable), int32(low), int32(high)); ok {
		return int(n)<<1 ^ flip
	}
	if len(b.nodes) >= b.budget || (b.stop != nil && b.stop.Load()) {
		b.exceeded = true
		return bddFalse
	}
	b.nodes = append(b.nodes, bddNode{variable: variable, low: low, high: high})
	n := len(b.nodes) - 1
	b.unique.insert(int32(variable), int32(low), int32(high), int32(n))
	return n<<1 ^ flip
}

// variable returns the edge for a single input variable.
func (b *bdd) variable(v int) int { return b.mk(v, bddFalse, bddTrue) }

// not is the complement bit: no node, no lookup.
func (b *bdd) not(a int) int { return a ^ 1 }

func (b *bdd) apply(op, x, y int) int {
	if b.exceeded {
		return bddFalse
	}
	// Terminal cases, an operand equal to the other's complement included
	// (Oak.BddComplement: and_self_not, or_self_not, xor_self_not, xor_true).
	switch op {
	case opAnd:
		if x == bddFalse || y == bddFalse {
			return bddFalse
		}
		if x == bddTrue {
			return y
		}
		if y == bddTrue {
			return x
		}
		if x == y {
			return x
		}
		if x == y^1 {
			return bddFalse
		}
	case opOr:
		if x == bddTrue || y == bddTrue {
			return bddTrue
		}
		if x == bddFalse {
			return y
		}
		if y == bddFalse {
			return x
		}
		if x == y {
			return x
		}
		if x == y^1 {
			return bddTrue
		}
	case opXor:
		if x == bddFalse {
			return y
		}
		if y == bddFalse {
			return x
		}
		if x == bddTrue {
			return y ^ 1
		}
		if y == bddTrue {
			return x ^ 1
		}
		if x == y {
			return bddFalse
		}
		if x == y^1 {
			return bddTrue
		}
	}
	if x > y && (op == opAnd || op == opOr || op == opXor) {
		x, y = y, x // commutative: canonical memo key
	}
	if r, ok := b.memo.lookup(int32(op), int32(x), int32(y)); ok {
		return int(r)
	}
	vx, vy := b.variableOf(x), b.variableOf(y)
	v := vx
	if vy < v {
		v = vy
	}
	xl, xh := x, x
	if vx == v {
		xl, xh = b.low(x), b.high(x)
	}
	yl, yh := y, y
	if vy == v {
		yl, yh = b.low(y), b.high(y)
	}
	r := b.mk(v, b.apply(op, xl, yl), b.apply(op, xh, yh))
	b.memo.insert(int32(op), int32(x), int32(y), int32(r))
	return r
}

// ite is if-then-else: (c ∧ t) ∨ (¬c ∧ e).
func (b *bdd) ite(c, t, e int) int {
	return b.apply(opOr, b.apply(opAnd, c, t), b.apply(opAnd, b.not(c), e))
}

// restrict is the cofactor of e at variable = value: the diagram with the
// variable's nodes replaced by the chosen branch (Oak.BddComplement's
// cofactors through complemented edges). Variables are ordered ascending
// from the root, so a subgraph rooted past the variable is unchanged.
func (b *bdd) restrict(e, variable int, value bool) int {
	memo := map[int]int{}
	var walk func(e int) int
	walk = func(e int) int {
		if e>>1 == 0 || b.variableOf(e) > variable {
			return e
		}
		if done, seen := memo[e]; seen {
			return done
		}
		var out int
		if b.variableOf(e) == variable {
			if value {
				out = b.high(e)
			} else {
				out = b.low(e)
			}
		} else {
			out = b.mk(b.variableOf(e), walk(b.low(e)), walk(b.high(e)))
		}
		memo[e] = out
		return out
	}
	return walk(e)
}

// satisfyingPath assigns variables along one path from n to the true
// terminal (every non-false node of a reduced BDD has such a path).
func (b *bdd) satisfyingPath(e int) map[int]bool {
	assignment := map[int]bool{}
	for e>>1 != 0 {
		variable := b.variableOf(e)
		if high := b.high(e); high != bddFalse {
			assignment[variable] = true
			e = high
		} else {
			assignment[variable] = false
			e = b.low(e)
		}
	}
	return assignment
}
