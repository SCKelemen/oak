package asm

import (
	"fmt"
	"testing"
)

// The shape of lean_reserved(rs_name(...)) as a premise: a chain of
// conditionals on a name's length (a 32-bit read) selecting disjunctions of
// point comparisons of its two 64-bit words against constants.
func TestReservedShapeBlast(t *testing.T) {
	lo, hi := paramTerm("loop2.lo", 64), paramTerm("loop2.hi", 64)
	n := selectTerm("rx", binaryTerm("add", paramTerm("raw.strings_at", 32), binaryTerm("shl", paramTerm("id", 32), constTerm(1, 32))), 32)
	point := func(c1, c2 uint64) *term {
		return binaryTerm("and", truncate(cmpTerm("eq", lo, constTerm(c1, 64)), 1), truncate(cmpTerm("eq", hi, constTerm(c2, 64)), 1))
	}
	var chain *term = constTerm(0, 1)
	seed := uint64(0x6E696174626F)
	for length := 14; length >= 2; length-- {
		var disj *term
		for k := 0; k < 4; k++ {
			seed = seed*6364136223846793005 + 1442695040888963407
			p := point(seed, seed>>40)
			if disj == nil {
				disj = p
			} else {
				disj = binaryTerm("or", disj, p)
			}
		}
		isLen := truncate(cmpTerm("eq", n, constTerm(uint64(length), 32)), 1)
		chain = iteTerm(isLen, binaryTerm("and", isLen, disj), chain)
	}
	names := []string{"id", "loop2.hi", "loop2.lo", "raw.strings_at"}
	widths := map[string]int{"id": 32, "loop2.hi": 64, "loop2.lo": 64, "raw.strings_at": 32}
	bl := newBlaster(names, widths)
	bl.bdd = newBDD(loopDecisionNodeBudget)
	if bits := bl.blast(chain); bits == nil || bl.bdd.exceeded {
		t.Fatalf("the reserved-word shape must blast within the decision's budget")
	}
	// Fifty-two point comparisons of two 64-bit words: a few hundred
	// nodes each once equality is bit by bit from the deepest literal up
	// (518,445 nodes through the subtractor and shallow-first chains).
	if got := len(bl.bdd.nodes); got > 60000 {
		t.Fatalf("the reserved-word shape took %d diagram nodes, want under 60000", got)
	}
	fmt.Printf("reserved shape: diagram %d nodes\n", len(bl.bdd.nodes))
	// The parts: the points alone (one length's disjunction), the chain
	// over a parameter length rather than a read.
	measure := func(label string, t *term, names []string, widths map[string]int) {
		bl := newBlaster(names, widths)
		bl.bdd = newBDD(loopDecisionNodeBudget)
		bits := bl.blast(t)
		nodes, _ := dagNodes(1<<20, t)
		fmt.Printf("%s: term %d nodes -> diagram %d nodes, exceeded=%v, nil=%v\n", label, nodes, len(bl.bdd.nodes), bl.bdd.exceeded, bits == nil)
	}
	var disj *term
	for k := 0; k < 4; k++ {
		seed = seed*6364136223846793005 + 1442695040888963407
		p := point(seed, seed>>40)
		if disj == nil {
			disj = p
		} else {
			disj = binaryTerm("or", disj, p)
		}
	}
	measure("four points", disj, names, widths)
	measure("one point", point(seed, seed>>40), names, widths)
	one := newBlaster(names, widths)
	one.bdd = newBDD(loopDecisionNodeBudget)
	one.blast(point(seed, seed>>40))
	if got := len(one.bdd.nodes); got > 1000 {
		t.Fatalf("one 128-bit point comparison took %d diagram nodes, want under 1000 (linear in the width)", got)
	}
	nParam := paramTerm("n", 32)
	var chainP *term = constTerm(0, 1)
	for length := 14; length >= 2; length-- {
		isLen := truncate(cmpTerm("eq", nParam, constTerm(uint64(length), 32)), 1)
		chainP = iteTerm(isLen, binaryTerm("and", isLen, disj), chainP)
	}
	namesP := append([]string{"n"}, names...)
	widthsP := map[string]int{"n": 32}
	for k, v := range widths {
		widthsP[k] = v
	}
	measure("chain over a parameter length, one disjunction", chainP, namesP, widthsP)
}
