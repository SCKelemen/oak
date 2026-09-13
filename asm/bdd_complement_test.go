package asm

import "testing"

// The complement-edge representation (Oak.BddComplement): every stored
// node's high edge is positive, negation is the complement bit, a function
// and its complement are one node, and the terminal identities hold as
// edges.
func TestComplementEdgeCanonicity(t *testing.T) {
	d := newBDD(blastNodeBudget)
	x := benchVector(d, 0, 2, 16)
	y := benchVector(d, 1, 2, 16)
	sum := benchAdd(d, x, y)
	prod := benchMultiply(d, x[:8], y[:8])
	for _, e := range append(sum, prod...) {
		if d.not(d.not(e)) != e {
			t.Fatalf("double complement of %d is %d", e, d.not(d.not(e)))
		}
		if d.apply(opXor, e, d.not(e)) != bddTrue || d.apply(opAnd, e, d.not(e)) != bddFalse || d.apply(opOr, e, d.not(e)) != bddTrue {
			t.Fatalf("edge %d: the terminal identities with its complement fail", e)
		}
		if d.apply(opXor, e, bddTrue) != d.not(e) {
			t.Fatalf("edge %d: xor with true is not the complement bit", e)
		}
	}
	for n, node := range d.nodes[1:] {
		if node.high&1 != 0 {
			t.Fatalf("node %d stores a complemented high edge %d", n+1, node.high)
		}
		if node.low == node.high {
			t.Fatalf("node %d is redundant", n+1)
		}
	}
	// A function and its negation share every node: complementing the
	// whole sum creates nothing.
	before := len(d.nodes)
	for _, e := range sum {
		_ = d.not(e)
	}
	if len(d.nodes) != before {
		t.Fatalf("negation created %d nodes", len(d.nodes)-before)
	}
	// A satisfying path of a complemented edge reaches true: the path for
	// not(x0 and x1) assigns some variable false.
	both := d.apply(opAnd, x[0], x[1])
	path := d.satisfyingPath(d.not(both))
	if len(path) == 0 {
		t.Fatalf("no path for the complement of x0 and x1")
	}
	value := true
	for _, v := range path {
		value = value && v
	}
	if value {
		t.Fatalf("the path %v satisfies x0 and x1, not its complement", path)
	}
}
