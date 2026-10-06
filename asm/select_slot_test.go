package asm

import (
	"fmt"
	"testing"
)

// An adder equality between a parameter sum and a read's value shifted:
// `le.state_at + 9 == le.strs_at + (ew[k] << 1)` (ident's culprit). The
// read's block interleaves with the parameters' bits while it is among the
// first selectSlots distinct reads; past them the blocks trail every
// parameter, and an adder across the two is exponential.
func TestSelectSlotInterleaving(t *testing.T) {
	state, strs := paramTerm("le.state_at", 32), paramTerm("le.strs_at", 32)
	names := []string{"id", "le.rnames_at", "le.state_at", "le.strs_at", "raw.strings_at"}
	widths := map[string]int{"id": 32, "le.rnames_at": 32, "le.state_at": 32, "le.strs_at": 32, "raw.strings_at": 32}
	measure := func(label string, priorReads int) int {
		bl := newBlaster(names, widths)
		bl.bdd = newBDD(loopDecisionNodeBudget)
		for k := 0; k < priorReads; k++ {
			bl.blast(selectTerm("ew", binaryTerm("add", state, constTerm(uint64(100+k), 32)), 32))
		}
		read := selectTerm("ew", binaryTerm("add", state, constTerm(8, 32)), 32)
		eq := truncate(cmpTerm("eq", binaryTerm("add", state, constTerm(9, 32)), binaryTerm("add", strs, binaryTerm("shl", read, constTerm(1, 32)))), 1)
		bits := bl.blast(eq)
		fmt.Printf("%s: %d diagram nodes (exceeded=%v, nil=%v)\n", label, len(bl.bdd.nodes), bl.bdd.exceeded, bits == nil)
		return len(bl.bdd.nodes)
	}
	first := measure("the read among the first slots", 0)
	ninth := measure("the ninth distinct read (ident's)", 8)
	if ninth > 8*first {
		t.Fatalf("the ninth read costs %d nodes against %d for the first: it must interleave with the parameters", ninth, first)
	}
	if proofSelectSlots < 32 {
		t.Fatalf("proofSelectSlots is %d; a premise's reads past it trail the parameters", proofSelectSlots)
	}
}
