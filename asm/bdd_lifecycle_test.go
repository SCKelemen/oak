package asm

import (
	"sync/atomic"
	"testing"
)

type bddStorage struct {
	nodes, nodeCapacity, unique, uniqueSlots, memo, memoSlots int
}

func storageOfBDD(b *bdd) bddStorage {
	return bddStorage{len(b.nodes), cap(b.nodes), b.unique.count, len(b.unique.entries), b.memo.count, len(b.memo.entries)}
}

func TestBDDStoppedFastPaths(t *testing.T) {
	for _, name := range []string{
		"unique hit", "redundant node", "binary terminal", "binary memo",
		"ite terminal", "ite memo", "restrict terminal", "restrict unchanged",
		"restrict recursive", "satisfying path", "assignment evaluation",
	} {
		t.Run(name, func(t *testing.T) {
			b := newBDD(1000)
			x, y, z := b.variable(0), b.variable(1), b.variable(2)
			xor := b.apply(opXor, x, y)
			b.ite(x, y, z)
			before := storageOfBDD(b)
			var stop atomic.Bool
			b.stop = &stop
			stop.Store(true)
			switch name {
			case "unique hit":
				b.variable(0)
			case "redundant node":
				b.mk(0, x, x)
			case "binary terminal":
				b.apply(opOr, bddTrue, x)
			case "binary memo":
				b.apply(opXor, x, y)
			case "ite terminal":
				b.ite(bddTrue, y, z)
			case "ite memo":
				b.ite(x, y, z)
			case "restrict terminal":
				if b.restrict(bddTrue, 0, true) != bddFalse {
					t.Fatal("cancelled restriction returned a result")
				}
			case "restrict unchanged":
				if b.restrict(y, 0, true) != bddFalse {
					t.Fatal("cancelled restriction returned a result")
				}
			case "restrict recursive":
				if b.restrict(xor, 1, true) != bddFalse {
					t.Fatal("cancelled restriction returned a result")
				}
			case "satisfying path":
				if path := b.satisfyingPath(xor); path != nil {
					t.Fatalf("cancelled path returned a partial assignment: %v", path)
				}
			case "assignment evaluation":
				if b.holdsUnder(xor, map[int]bool{0: true}) {
					t.Fatal("cancelled evaluation returned a result")
				}
			}
			if !b.exceeded {
				t.Fatal("fast path ignored cancellation")
			}
			if after := storageOfBDD(b); after != before {
				t.Fatalf("storage changed after stop: before %+v, after %+v", before, after)
			}
			// Cancellation is sticky: a partial diagram cannot become valid
			// merely because somebody reuses the stop flag.
			stop.Store(false)
			if !b.interrupted() {
				t.Fatal("interrupted diagram became usable again")
			}
		})
	}
}

// Every Boolean function of four variables already exists here. All the XOR
// results therefore hit the unique table, which used to bypass both the stop
// flag and the node limit while growing a separate unbounded operation memo.
func TestBDDStoppedExistingNodesDoNotGrowMemo(t *testing.T) {
	b := newBDD(40000)
	var build func(uint16, int) int
	build = func(truth uint16, variable int) int {
		if variable == 4 {
			return int(truth & 1)
		}
		bits := 1 << (3 - variable)
		return b.mk(variable, build(truth&uint16((1<<bits)-1), variable+1), build(truth>>bits, variable+1))
	}
	roots := make([]int, 1<<16)
	for truth := range roots {
		roots[truth] = build(uint16(truth), 0)
	}
	if b.exceeded || len(b.nodes) != 32768 {
		t.Fatalf("incomplete universe: %d nodes, exceeded=%v", len(b.nodes), b.exceeded)
	}
	b.budget = len(b.nodes)
	// A full node allowance still permits valid existing-node operations.
	if got := b.apply(opXor, roots[0x35a7], roots[0x8751]); got != roots[0x35a7^0x8751] || b.exceeded {
		t.Fatal("node allowance incorrectly rejects an existing result")
	}
	before := storageOfBDD(b)
	var stop atomic.Bool
	b.stop = &stop
	stop.Store(true)
	seed := uint32(1)
	for i := 0; i < 250000; i++ {
		seed = seed*1664525 + 1013904223
		x := uint16(seed >> 8)
		seed = seed*1664525 + 1013904223
		y := uint16(seed >> 8)
		b.apply(opXor, roots[x], roots[y])
	}
	if !b.exceeded {
		t.Fatal("existing-node operations ignored stop")
	}
	if after := storageOfBDD(b); after != before {
		t.Fatalf("stopped memo grew: before %+v, after %+v", before, after)
	}
}

func TestBDDExhaustionDoesNotMemoizePartialResults(t *testing.T) {
	for _, operation := range []string{"binary", "ite"} {
		t.Run(operation, func(t *testing.T) {
			b := newBDD(4)
			x, y, z := b.variable(0), b.variable(1), b.variable(2)
			before := storageOfBDD(b)
			if operation == "binary" {
				b.apply(opAnd, x, y)
			} else {
				b.ite(x, y, z)
			}
			if !b.exceeded {
				t.Fatal("new node did not exhaust the exact node allowance")
			}
			if after := storageOfBDD(b); after != before {
				t.Fatalf("partial result was stored: before %+v, after %+v", before, after)
			}
			b.mk(0, x, x)
			b.apply(opXor, x, y)
			b.ite(x, y, z)
			if after := storageOfBDD(b); after != before {
				t.Fatalf("exhausted diagram kept growing: before %+v, after %+v", before, after)
			}
		})
	}
}

func TestBDDRehashCancellationPreservesTables(t *testing.T) {
	never := func() bool { return false }
	u, m := newUniqueTable(4096), newOpTable(4096)
	for i := int32(0); i < 2048; i++ {
		u.insert(i, 0, 1, i, never)
		m.insert(opXor, i, i+1, i, never)
	}
	for _, name := range []string{"unique", "memo"} {
		t.Run(name, func(t *testing.T) {
			polls := 0
			interrupted := func() bool { polls++; return polls == 4 }
			if name == "unique" {
				original := &u.entries[0]
				if u.insert(3000, 0, 1, 3000, interrupted) || &u.entries[0] != original || u.count != 2048 {
					t.Fatal("interrupted unique growth published a partial table")
				}
			} else {
				original := &m.entries[0]
				if m.insert(opXor, 3000, 3001, 3000, interrupted) || &m.entries[0] != original || m.count != 2048 {
					t.Fatal("interrupted memo growth published a partial table")
				}
			}
			if polls != 4 {
				t.Fatalf("rehash did not poll during traversal: %d polls", polls)
			}
		})
	}
	if !u.insert(3000, 0, 1, 3000, never) || !m.insert(opXor, 3000, 3001, 3000, never) {
		t.Fatal("undamaged tables could not grow after an interrupted rehash")
	}
	if result, ok := u.lookup(3000, 0, 1); !ok || result != 3000 || u.count != 2049 {
		t.Fatal("unique table lost the successful retry")
	}
	if result, ok := m.lookup(opXor, 3000, 3001); !ok || result != 3000 || m.count != 2049 {
		t.Fatal("memo table lost the successful retry")
	}
	for i := int32(0); i < 2048; i++ {
		if result, ok := u.lookup(i, 0, 1); !ok || result != i {
			t.Fatal("unique entry lost after interrupted growth")
		}
		if result, ok := m.lookup(opXor, i, i+1); !ok || result != i {
			t.Fatal("memo entry lost after interrupted growth")
		}
	}
}

func TestBDDBinarySemantics(t *testing.T) {
	b := newBDD(1000)
	var functions [256]int
	for table := range functions {
		var build func(int, int) int
		build = func(variable, prefix int) int {
			if variable == 3 {
				return table >> prefix & 1
			}
			return b.mk(variable, build(variable+1, prefix), build(variable+1, prefix|1<<variable))
		}
		functions[table] = build(0, 0)
	}
	for a, x := range functions {
		for c, y := range functions {
			for _, tc := range []struct{ op, want int }{{opAnd, a & c}, {opOr, a | c}, {opXor, a ^ c}} {
				if got := b.apply(tc.op, x, y); got != functions[tc.want] {
					t.Fatalf("operation %d on truth tables %02x,%02x: edge %d, want %d", tc.op, a, c, got, functions[tc.want])
				}
			}
		}
	}
	if b.exceeded {
		t.Fatal("unexpected budget exhaustion")
	}
}
