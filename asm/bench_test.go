package asm

import "testing"

// The BDD engine's baselines (docs/notes/formal-methods-performance-2026-09.md
// section 4, item 2), on circuits the blaster builds for every arithmetic
// theorem: a ripple-carry adder over two vectors of fresh variables
// (interleaved order, the grouped order blast.go picks), and a shift-and-add
// multiplier. Each benchmark builds the diagram from an empty engine and
// reports nodes per second, so a change to the tables shows as throughput
// and a change to the circuits as a smaller node count.

func benchVector(b *bdd, first, stride, bits int) []int {
	v := make([]int, bits)
	for i := range v {
		v[i] = b.variable(first + i*stride)
	}
	return v
}

func benchAdd(b *bdd, x, y []int) []int {
	sum := make([]int, len(x))
	carry := bddFalse
	for i := range x {
		xy := b.apply(opXor, x[i], y[i])
		sum[i] = b.apply(opXor, xy, carry)
		carry = b.apply(opOr, b.apply(opAnd, x[i], y[i]), b.apply(opAnd, xy, carry))
	}
	return sum
}

func benchMultiply(b *bdd, x, y []int) []int {
	acc := make([]int, len(x))
	for i := range acc {
		acc[i] = bddFalse
	}
	for i := range y {
		partial := make([]int, len(x))
		for j := range x {
			if j < i {
				partial[j] = bddFalse
			} else {
				partial[j] = b.apply(opAnd, x[j-i], y[i])
			}
		}
		acc = benchAdd(b, acc, partial)
	}
	return acc
}

func benchEqual(b *bdd, x, y []int) int {
	eq := bddTrue
	for i := range x {
		eq = b.apply(opAnd, eq, b.not(b.apply(opXor, x[i], y[i])))
	}
	return eq
}

func benchmarkCircuit(b *testing.B, bits int, build func(*bdd, []int, []int) int) {
	var nodes int
	for i := 0; i < b.N; i++ {
		d := newBDD(blastNodeBudget)
		x := benchVector(d, 0, 2, bits)
		y := benchVector(d, 1, 2, bits)
		if build(d, x, y) != bddTrue || d.exceeded {
			b.Fatal("the circuit identity did not reduce to true")
		}
		nodes = len(d.nodes)
	}
	b.ReportMetric(float64(nodes), "nodes")
	b.ReportMetric(float64(nodes)*float64(b.N)/b.Elapsed().Seconds(), "nodes/s")
}

// x + y == y + x, the adder built twice.
func addCommutes(d *bdd, x, y []int) int { return benchEqual(d, benchAdd(d, x, y), benchAdd(d, y, x)) }

// x * y == y * x, the multiplier built twice.
func mulCommutes(d *bdd, x, y []int) int {
	return benchEqual(d, benchMultiply(d, x, y), benchMultiply(d, y, x))
}

func BenchmarkBDDAdd32(b *testing.B) { benchmarkCircuit(b, 32, addCommutes) }
func BenchmarkBDDAdd64(b *testing.B) { benchmarkCircuit(b, 64, addCommutes) }
func BenchmarkBDDMul8(b *testing.B)  { benchmarkCircuit(b, 8, mulCommutes) }
func BenchmarkBDDMul12(b *testing.B) { benchmarkCircuit(b, 12, mulCommutes) }
