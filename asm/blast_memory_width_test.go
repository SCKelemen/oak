package asm

import (
	"fmt"
	"reflect"
	"sync/atomic"
	"testing"
)

// Raw memory nodes preserve the conflicting widths that ordinary typed
// constructors avoid. These controls exercise the real bit blaster, not a
// structural-equality shortcut. All diagrams have a small fixture ceiling.
const memoryWidthFixtureBudget = 8192

func memoryWidthRead(span string, index *term, width int) *term {
	return &term{kind: termSelect, name: span, left: index, width: width}
}

func memoryWidthEq(left, right *term) *term {
	return &term{kind: termCmp, op: "eq", width: 1, left: left, right: right}
}

func memoryWidthBlaster(cnf bool, names []string, widths map[string]int) *blaster {
	if cnf {
		return newCNFBlaster(names, widths)
	}
	return newBlaster(names, widths).withBudget(memoryWidthFixtureBudget)
}

func TestBlastMemoryWidthRejectsConflictingReads(t *testing.T) {
	for _, cnf := range []bool{false, true} {
		for _, reverse := range []bool{false, true} {
			for _, indexKind := range []string{"same", "different", "disjoint"} {
				t.Run(fmt.Sprintf("cnf=%v/reverse=%v/%s", cnf, reverse, indexKind), func(t *testing.T) {
					i, j := paramTerm("i", 2), paramTerm("j", 2)
					other := i
					switch indexKind {
					case "different":
						other = j
					case "disjoint":
						other = binaryTerm("add", zeroExtend(i, 32), constTerm(1, 32))
					}
					a, b := memoryWidthRead("mem", i, 4), memoryWidthRead("mem", other, 8)
					if reverse {
						a, b = b, a
					}
					bl := memoryWidthBlaster(cnf, []string{"i", "j"}, map[string]int{"i": 2, "j": 2})
					// Warm both indices so rejection itself must not allocate
					// variables, change ownership, or reserve a second slot.
					if bl.blast(a.left) == nil || bl.blast(b.left) == nil || bl.blast(a) == nil {
						t.Fatal("fixed-width first read failed")
					}
					owners := make(map[int]variableOwner, len(bl.owners))
					for variable, owner := range bl.owners {
						owners[variable] = owner
					}
					memo := len(bl.memo)
					if got := bl.blast(b); got != nil || !bl.exceeded() || len(bl.selects) != 1 || len(bl.memo) != memo || !reflect.DeepEqual(bl.owners, owners) {
						t.Fatal("conflicting width was admitted or changed slot/memo/owner state")
					}
					if bl.blast(a) != nil || bl.consistency() != bddFalse {
						t.Fatal("a cached result or consistency escaped the refusal latch")
					}
					if cnf {
						if len(bl.cnf.gates) > memoryWidthFixtureBudget {
							t.Fatal("CNF fixture exceeded its size ceiling")
						}
					} else if bl.bdd.budget != memoryWidthFixtureBudget || bl.bdd.memoryExhausted {
						t.Fatal("width rejection changed allowance or claimed admission exhaustion")
					}
				})
			}
		}
	}
}

func TestBlastMemoryWidthConcreteCounterexampleAndUnknown(t *testing.T) {
	i := paramTerm("i", 2)
	a := memoryWidthEq(memoryWidthRead("mem", i, 4), constTerm(0, 4))
	b := memoryWidthEq(memoryWidthRead("mem", i, 8), constTerm(0, 8))
	env := map[string]uint64{"i": 3, "mem[3]": 16}
	if a.eval(env) != 1 || b.eval(env) != 0 {
		t.Fatal("the concrete mixed-width counterexample no longer distinguishes the predicates")
	}
	for _, reverse := range []bool{false, true} {
		left, right := a, b
		if reverse {
			left, right = right, left
		}
		bl := newBlaster([]string{"i"}, map[string]int{"i": 2}).withBudget(memoryWidthFixtureBudget)
		if holds, decided := impliesEqualUnder(bl, constTerm(1, 1), left, right, 1); holds || decided || !bl.exceeded() {
			t.Fatal("mixed-width BDD equality became a proof or refutation instead of Unknown")
		}
		out, reason, ok := exportTermCNF("memory-width refusal", []string{"i"}, map[string]int{"i": 2}, memoryWidthEq(left, right), nil)
		if ok || reason == "" || out.Settled != nil || out.Text != "" || out.Variables != 0 || out.Clauses != 0 {
			t.Fatal("mixed-width CNF export published a settled result or partial formula")
		}
	}
}

func TestBlastMemoryWidthRejectsConflictingElementDomains(t *testing.T) {
	for _, element := range []struct{ span, parameter string }{
		{"mem", "mem[3]"},
		{"records.field", "records[3].field"},
		{"records.nested.field", "records[3].nested.field"},
	} {
		for _, cnf := range []bool{false, true} {
			for _, widths := range [][2]int{{4, 8}, {8, 4}} {
				for _, parameterFirst := range []bool{false, true} {
					t.Run(fmt.Sprintf("%s/cnf=%v/%d,%d/parameter-first=%v", element.span, cnf, widths[0], widths[1], parameterFirst), func(t *testing.T) {
						i := paramTerm("i", 2)
						read := memoryWidthRead(element.span, i, widths[0])
						parameter := paramTerm(element.parameter, widths[1])
						bl := memoryWidthBlaster(cnf, []string{"i", element.parameter}, map[string]int{"i": 2, element.parameter: widths[1]})
						if parameterFirst && bl.blast(parameter) == nil {
							t.Fatal("ordinary element parameter failed before the memory read")
						}
						if bl.blast(read) != nil || !bl.exceeded() || len(bl.selects) != 0 {
							t.Fatal("symbolic read with a conflicting element domain acquired a slot")
						}
						if _, cached := bl.memo[read]; cached {
							t.Fatal("refused read entered the term memo")
						}
					})
				}
			}
		}
	}
}

func TestBlastMemoryWidthFixedWidthAndExplicitViews(t *testing.T) {
	for _, width := range []int{4, 8, 32, 64} {
		i, j := paramTerm("i", 2), paramTerm("j", 2)
		read := memoryWidthRead("mem", i, width)
		other := memoryWidthRead("mem", j, width)
		bl := newBlaster([]string{"i", "j"}, map[string]int{"i": 2, "j": 2}).withBudget(memoryWidthFixtureBudget)
		if holds, decided := impliesEqualUnder(bl, memoryWidthEq(i, j), read, other, width); !holds || !decided || bl.exceeded() {
			t.Fatalf("fixed-width congruence failed at width %d", width)
		}
		for _, cnf := range []bool{false, true} {
			bl := memoryWidthBlaster(cnf, []string{"i"}, map[string]int{"i": 2})
			first := bl.blast(read)
			again := bl.blast(memoryWidthRead("mem", i, width))
			if len(first) != width || !reflect.DeepEqual(first, again) || len(bl.selects) != 1 || bl.exceeded() {
				t.Fatal("same-width exact-index reads no longer share one slot")
			}
		}
	}
	for _, width := range []int{4, 8} {
		for _, useWidth := range []int{2, 16} {
			i := paramTerm("i", 2)
			read := memoryWidthRead("mem", i, width)
			parameter := paramTerm("mem[3]", width)
			left, right := truncate(read, useWidth), truncate(parameter, useWidth)
			if useWidth > width {
				left, right = zeroExtend(read, useWidth), zeroExtend(parameter, useWidth)
			}
			cnf := newCNFBlaster([]string{"i", "mem[3]"}, map[string]int{"i": 2, "mem[3]": width})
			if len(cnf.blast(left)) != useWidth || len(cnf.blast(right)) != useWidth || cnf.exceeded() || len(cnf.selects) != 1 || len(cnf.selects[0].vars) != width {
				t.Fatal("legal explicit views failed in the shared CNF lowering")
			}
			bl := newBlaster([]string{"i", "mem[3]"}, map[string]int{"i": 2, "mem[3]": width}).withBudget(memoryWidthFixtureBudget)
			if holds, decided := impliesEqualUnder(bl, memoryWidthEq(i, constTerm(3, 2)), left, right, useWidth); !holds || !decided || bl.exceeded() || len(bl.selects) != 1 || len(bl.selects[0].vars) != width {
				t.Fatalf("legal explicit memory view failed: element=%d use=%d", width, useWidth)
			}
			for value := uint64(0); value < 1<<uint(width); value++ {
				env := map[string]uint64{"i": 3, "mem[3]": value}
				if left.eval(env) != right.eval(env) {
					t.Fatal("legal explicit-view fixture is not concretely equal")
				}
			}
		}
	}
}

func TestBlastMemoryWidthDifferentSpansRemainIndependent(t *testing.T) {
	i := paramTerm("i", 2)
	for _, cnf := range []bool{false, true} {
		bl := memoryWidthBlaster(cnf, []string{"i", "other[3]", "records[3].byte", "records[3].word"}, map[string]int{"i": 2, "other[3]": 16, "records[3].byte": 8, "records[3].word": 32})
		for _, read := range []*term{memoryWidthRead("mem", i, 4), memoryWidthRead("different", i, 8), memoryWidthRead("records.byte", i, 8), memoryWidthRead("records.word", i, 32)} {
			if bl.blast(read) == nil || bl.exceeded() {
				t.Fatal("independent memory spans acquired a shared element width")
			}
		}
		if len(bl.selects) != 4 {
			t.Fatal("independent spans unexpectedly shared slots")
		}
	}
}

func TestBlastMemoryWidthRejectsBeforeComponentSlotPlacement(t *testing.T) {
	i := paramTerm("i", 2)
	bl := newComponentBlaster([]string{"i"}, map[string]int{"i": 2}, map[string]string{"i": "data"}, []string{"data"}, map[string]int{"data": 2}, func(string, *term) (string, bool) {
		return "data", true
	}).withBudget(memoryWidthFixtureBudget)
	if bl.blast(memoryWidthRead("mem", i, 4)) == nil || len(bl.slotPlaces) != 1 || bl.blockUsed["data"] != 1 {
		t.Fatal("first component slot was not placed")
	}
	if bl.blast(memoryWidthRead("mem", i, 8)) != nil || !bl.exceeded() || len(bl.selects) != 1 || len(bl.slotPlaces) != 1 || bl.blockUsed["data"] != 1 || bl.trailUsed != 0 {
		t.Fatal("refused width consumed a component or trailing slot")
	}
}

func TestBlastMemoryWidthNarrowedDomainIsConservativeUnknown(t *testing.T) {
	i, element := paramTerm("i", 2), paramTerm("mem[3]", 8)
	read := memoryWidthRead("mem", i, 8)
	bound := &term{kind: termCmp, op: "lo", width: 1, left: element, right: constTerm(16, 8)}
	premise := binaryTerm("and", memoryWidthEq(i, constTerm(3, 2)), bound)
	widths := map[string]int{"i": 2, "mem[3]": 8}
	narrowByPremise(premise, widths)
	if widths["mem[3]"] != 4 || element.declaredWidth() != 8 {
		t.Fatal("fixture did not distinguish the narrowed domain from the declaration")
	}
	for value := uint64(0); value < 16; value++ {
		env := map[string]uint64{"i": 3, "mem[3]": value}
		if premise.eval(env) != 1 || read.eval(env) != element.eval(env) {
			t.Fatal("the conservatively refused obligation is not valid on its narrowed domain")
		}
	}
	// widths carries effective solver bounds, not immutable declaration
	// provenance. Refuse this legal case too rather than guessing why the
	// widths differ and admitting an untyped mixed-width memory relation.
	bl := newBlaster([]string{"i", "mem[3]"}, widths).withBudget(memoryWidthFixtureBudget)
	if holds, decided := impliesEqualUnder(bl, premise, read, element, 8); holds || decided || !bl.exceeded() {
		t.Fatal("the guard silently reinterpreted a differing effective memory domain")
	}
}

func TestBlastMemoryWidthRefusalFreshAndCancellation(t *testing.T) {
	i := paramTerm("i", 2)
	bl := newBlaster([]string{"i"}, map[string]int{"i": 2}).withBudget(memoryWidthFixtureBudget)
	if bl.blast(memoryWidthRead("mem", i, 4)) == nil || bl.blast(memoryWidthRead("mem", i, 8)) != nil || !bl.exceeded() {
		t.Fatal("fixture failed to latch a conflicting width")
	}
	fresh := bl.fresh(memoryWidthFixtureBudget)
	if fresh.blast(memoryWidthRead("mem", i, 8)) == nil || fresh.exceeded() || !bl.exceeded() || len(fresh.selects) != 1 || len(fresh.selects[0].vars) != 8 {
		t.Fatal("a fresh owner retained or cleared another owner's refused span")
	}
	var stop atomic.Bool
	stop.Store(true)
	fresh.bdd.stop = &stop
	nodes, memo, slots, owners := len(fresh.bdd.nodes), len(fresh.memo), len(fresh.selects), len(fresh.owners)
	if fresh.selectBits("mem", nil, 4, i) != nil || !fresh.exceeded() || len(fresh.bdd.nodes) != nodes || len(fresh.memo) != memo || len(fresh.selects) != slots || len(fresh.owners) != owners {
		t.Fatal("cancelled select admission bypassed its latch or mutated ownership")
	}
}
