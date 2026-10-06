package asm

import "testing"

// A machine condition settled branch by branch against the source's one
// comparison over the merged value: the one-sided arm rule proves it
// without a diagram of the merged value, and leaves a side whose arm
// differs undecided rather than proven.
func TestOneSidedArmsProvesSplitComparison(t *testing.T) {
	k, x, y := paramTerm("k", 32), paramTerm("x", 32), paramTerm("y", 32)
	c := cmpTerm("lo", paramTerm("p", 32), constTerm(7, 32))
	merged := cmpTerm("lo", k, iteTerm(c, x, y))
	split := iteTerm(c, cmpTerm("lo", k, x), cmpTerm("lo", k, y))
	widthOf := func(string) int { return 32 }
	budget := &nodeBudget{remaining: loopProofNodeBudget, loop: true}
	if holds, decided := impliesEqualOneSidedArms(constTerm(1, 1), merged, split, widthOf, budget, 0); !decided || !holds {
		t.Fatalf("one-sided arms over a split comparison: holds=%v decided=%v", holds, decided)
	}
	wrong := iteTerm(c, cmpTerm("lo", k, x), cmpTerm("lo", k, x))
	if holds, decided := impliesEqualOneSidedArms(constTerm(1, 1), merged, wrong, widthOf, budget, 0); decided && holds {
		t.Fatalf("one-sided arms proved a side whose other arm differs")
	}
}

// The canonical forms the ident replay exposed and the stage2 pilot kept:
// a term compared with itself folds (not a parameter's narrow view against
// its full value), and a conditional with complementary arms is the
// complement of the other.
func TestCanonicalSelfComparisonAndComplement(t *testing.T) {
	x, y := paramTerm("x", 32), paramTerm("y", 32)
	sum := binaryTerm("add", x, constTerm(9, 32))
	sum2 := binaryTerm("add", paramTerm("x", 32), constTerm(9, 32))
	if got := canonical(cmpTerm("eq", sum, sum2)); got.kind != termConst || got.value != 1 {
		t.Fatalf("x + 9 == x + 9 canonicalizes to %s, want 1", got)
	}
	if got := canonical(cmpTerm("lo", sum, sum2)); got.kind != termConst || got.value != 0 {
		t.Fatalf("x + 9 < x + 9 canonicalizes to %s, want 0", got)
	}
	narrow := &term{kind: termParam, width: 32, name: "x", declared: 16}
	if got := canonical(cmpTerm("eq", x, narrow)); got.kind == termConst {
		t.Fatalf("x == (x at 16 bits) folded to %s", got)
	}
	p := cmpTerm("eq", paramTerm("p", 32), constTerm(0, 32))
	a := iteTerm(p, cmpTerm("eq", x, constTerm(0, 32)), cmpTerm("eq", y, x))
	b := iteTerm(p, cmpTerm("ne", x, constTerm(0, 32)), cmpTerm("ne", y, x))
	if !complementary(a, b) {
		t.Fatalf("pointwise complementary conditionals not recognized")
	}
	if complementary(a, iteTerm(p, cmpTerm("ne", x, constTerm(0, 32)), cmpTerm("eq", y, x))) {
		t.Fatalf("conditionals complementary in one arm only were taken as complementary")
	}
}

// Components apart: the table's words stand in blocks of their own, the
// length read gets a block, and the arena offsets interleave in the last.
func TestComponentBlasterBlocks(t *testing.T) {
	id, state, rnames := paramTerm("id", 32), paramTerm("state", 32), paramTerm("rnames", 32)
	lo, hi := paramTerm("lo", 64), paramTerm("hi", 64)
	length := selectTerm("rx", binaryTerm("add", binaryTerm("shl", id, constTerm(1, 32)), constTerm(1, 32)), 32)
	table := iteTerm(cmpTerm("eq", length, constTerm(2, 32)), binaryTerm("and", cmpTerm("eq", lo, constTerm(29793, 64)), cmpTerm("eq", hi, constTerm(0, 64))), constTerm(0, 1))
	offsets := cmpTerm("eq", binaryTerm("add", rnames, id), state)
	premise := binaryTerm("and", table, offsets)
	a := cmpTerm("eq", selectTerm("ew", state, 32), constTerm(0, 32))
	b := cmpTerm("eq", selectTerm("ew", binaryTerm("add", rnames, id), 32), constTerm(0, 32))
	names := []string{"hi", "id", "lo", "rnames", "state"}
	widths := map[string]int{"hi": 64, "id": 32, "lo": 64, "rnames": 32, "state": 32}
	bl := componentBlaster(names, widths, premise, a, b)
	if bl == nil {
		t.Fatalf("no components-apart order for a premise in two parts")
	}
	if bl.blockOf["lo"] == bl.blockOf["state"] || bl.blockOf["hi"] == bl.blockOf["state"] {
		t.Fatalf("the table's words share the offsets' block: %v", bl.blockOf)
	}
	if bl.blockOf["id"] != bl.blockOf["state"] || bl.blockOf["rnames"] != bl.blockOf["state"] {
		t.Fatalf("the offsets of one comparison are apart: %v", bl.blockOf)
	}
	if lastBlock := bl.blockOf["state"]; bl.blockBase[lastBlock] <= bl.blockBase[bl.blockOf["lo"]] {
		t.Fatalf("the sides' block is not last: bases %v", bl.blockBase)
	}
	bl.bdd = newBDD(blastNodeBudget)
	bits := bl.blast(binaryTerm("and", premise, binaryTerm("and", a, b)))
	if bits == nil || bl.bdd.exceeded {
		t.Fatalf("the components-apart order did not blast the premise and sides")
	}
	if len(bl.selects) != 3 || len(bl.slotPlaces) != 3 {
		t.Fatalf("%d reads met, %d placed", len(bl.selects), len(bl.slotPlaces))
	}
}
