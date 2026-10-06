package asm

import (
	"testing"
	"time"
)

// Truncating a wide combination of 1/0 values to one bit pushes the
// truncation to its operands. The operands' truncations are one node per
// operand (canonicalTable.bitOf), so a shared subgraph is canonicalized
// once: here every level reads the one below twice, 2^48 paths over 49
// levels, the shape of a guarded scan's unrolled selection that a caller
// mutates through (OS OAK-REQUEST #16), which a fresh truncation per visit
// walked path by path and never finished.
func TestCanonicalBitTruncationKeepsSharing(t *testing.T) {
	a := paramTerm("a", 8)
	x := zeroExtend(cmpTerm("eq", a, constTerm(0, 8)), 8)
	for k := 1; k <= 48; k++ {
		c := zeroExtend(cmpTerm("eq", a, constTerm(uint64(k), 8)), 8)
		x = binaryTerm("or", binaryTerm("and", x, c), binaryTerm("xor", x, c))
	}
	wide := x
	done := make(chan *term, 1)
	go func() { done <- canonical(truncate(wide, 1)) }()
	select {
	case got := <-done:
		for _, v := range []uint64{0, 1, 7, 48, 49, 255} {
			env := map[string]uint64{"a": v}
			if want := wide.eval(env) & 1; got.eval(env) != want {
				t.Fatalf("a=%d: canonical bit %d, want %d", v, got.eval(env), want)
			}
		}
	case <-time.After(60 * time.Second):
		t.Fatal("canonicalizing the shared truncation did not finish: the walk lost the subgraph's sharing")
	}
}
