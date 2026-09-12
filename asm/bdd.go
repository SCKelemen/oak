package asm

import "sync/atomic"

// A small reduced ordered binary decision diagram (ROBDD) for the §8
// verifier's bit-blaster (docs/spec/94-assembler.md). Nodes are canonical:
// two equal boolean functions are the same node index, so equivalence of
// two blasted terms is index equality per bit, and a differing bit yields a
// concrete counterexample by walking a path to the true terminal. A node
// budget keeps blow-up fail-closed: when exceeded, the caller keeps the
// labeled witness-checked verdict instead of claiming proof.

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

type bddKey struct{ variable, low, high int }
type bddOpKey struct{ op, a, b int }

type bdd struct {
	nodes    []bddNode
	unique   map[bddKey]int
	memo     map[bddOpKey]int
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
	b := &bdd{unique: map[bddKey]int{}, memo: map[bddOpKey]int{}, budget: budget}
	b.nodes = []bddNode{{variable: bddTerminalVar}, {variable: bddTerminalVar}}
	return b
}

func (b *bdd) variableOf(n int) int { return b.nodes[n].variable }

// mk returns the canonical node for (variable, low, high).
func (b *bdd) mk(variable, low, high int) int {
	if low == high {
		return low
	}
	key := bddKey{variable, low, high}
	if n, ok := b.unique[key]; ok {
		return n
	}
	if len(b.nodes) >= b.budget || (b.stop != nil && b.stop.Load()) {
		b.exceeded = true
		return bddFalse
	}
	b.nodes = append(b.nodes, bddNode{variable: variable, low: low, high: high})
	n := len(b.nodes) - 1
	b.unique[key] = n
	return n
}

// variable returns the node for a single input variable.
func (b *bdd) variable(v int) int { return b.mk(v, bddFalse, bddTrue) }

func (b *bdd) not(a int) int { return b.apply(opXor, a, bddTrue) }

func (b *bdd) apply(op, x, y int) int {
	if b.exceeded {
		return bddFalse
	}
	// Terminal cases.
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
	case opXor:
		if x == bddFalse {
			return y
		}
		if y == bddFalse {
			return x
		}
		if x == y {
			return bddFalse
		}
		if x == bddTrue && y == bddTrue {
			return bddFalse
		}
	}
	if x > y && (op == opAnd || op == opOr || op == opXor) {
		x, y = y, x // commutative: canonical memo key
	}
	key := bddOpKey{op, x, y}
	if r, ok := b.memo[key]; ok {
		return r
	}
	vx, vy := b.variableOf(x), b.variableOf(y)
	v := vx
	if vy < v {
		v = vy
	}
	xl, xh := x, x
	if vx == v {
		xl, xh = b.nodes[x].low, b.nodes[x].high
	}
	yl, yh := y, y
	if vy == v {
		yl, yh = b.nodes[y].low, b.nodes[y].high
	}
	r := b.mk(v, b.apply(op, xl, yl), b.apply(op, xh, yh))
	b.memo[key] = r
	return r
}

// ite is if-then-else: (c ∧ t) ∨ (¬c ∧ e).
func (b *bdd) ite(c, t, e int) int {
	return b.apply(opOr, b.apply(opAnd, c, t), b.apply(opAnd, b.not(c), e))
}

// satisfyingPath assigns variables along one path from n to the true
// terminal (every non-false node of a reduced BDD has such a path).
func (b *bdd) satisfyingPath(n int) map[int]bool {
	assignment := map[int]bool{}
	for n != bddTrue && n != bddFalse {
		node := b.nodes[n]
		if node.high != bddFalse {
			assignment[node.variable] = true
			n = node.high
		} else {
			assignment[node.variable] = false
			n = node.low
		}
	}
	return assignment
}
