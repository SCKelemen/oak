package asm

import (
	"runtime"
	"sync/atomic"
	"testing"
	"time"
)

func TestBDDOrderRaceJoinsCancelledWorkers(t *testing.T) {
	// Exercise the production helper used by the normal equality race,
	// escalated equality race, and theorem decider, not a copy of its loop.
	for iteration := 0; iteration < 10; iteration++ {
		blasters := []*blaster{newBlaster(nil, nil), newBlaster(nil, nil), newBlaster(nil, nil)}
		started, cancelled, release := make(chan struct{}), make(chan struct{}), make(chan struct{})
		returned := make(chan bool, 1)
		var finished atomic.Int32
		go func() {
			result, decided := raceBDDOrders(blasters, func(bl *blaster) (int, bool) {
				defer finished.Add(1)
				if bl == blasters[0] {
					<-started
					return 7, false
				}
				if bl == blasters[2] {
					return 99, true // an undecided result cannot win
				}
				close(started)
				for !bl.bdd.stop.Load() {
					runtime.Gosched()
				}
				close(cancelled)
				<-release
				// Deliberately omit reporting cancellation. The helper's own
				// final check must still reject this placeholder result.
				return -1, false
			})
			returned <- decided && result == 7
		}()
		select {
		case <-cancelled:
		case <-time.After(5 * time.Second):
			close(release)
			t.Fatal("winning result did not cancel the other order")
		}
		select {
		case <-returned:
			close(release)
			t.Fatal("production race returned while a losing worker still owned its store")
		case <-time.After(10 * time.Millisecond):
		}
		close(release)
		select {
		case valid := <-returned:
			if !valid || finished.Load() != int32(len(blasters)) {
				t.Fatalf("winner/worker cleanup: valid=%v finished=%d", valid, finished.Load())
			}
		case <-time.After(5 * time.Second):
			t.Fatal("race did not return after every worker finished")
		}
	}
}

func TestBDDOrderRaceAllExhausted(t *testing.T) {
	for _, count := range []int{0, 1, 4} {
		blasters := make([]*blaster, count)
		for i := range blasters {
			blasters[i] = newBlaster(nil, nil)
		}
		if _, decided := raceBDDOrders(blasters, func(bl *blaster) (int, bool) {
			bl.bdd.exceeded = true
			return 1, false // even a misreported placeholder cannot win
		}); decided {
			t.Fatalf("%d exhausted orders produced a decision", count)
		}
	}
}

func TestBDDStoppedCachedBlastsFailClosed(t *testing.T) {
	names, widths := []string{"x"}, map[string]int{"x": 4}
	x := paramTerm("x", 4)
	for _, operation := range []string{"blast", "equality", "theorem", "implication"} {
		t.Run(operation, func(t *testing.T) {
			bl := newBlaster(names, widths)
			claim := cmpTerm("eq", x, constTerm(3, 4))
			evaluator := newTermEvaluator(claim)
			if bl.blast(x) == nil || bl.blast(claim) == nil {
				t.Fatal("unable to prime cache")
			}
			before, terms := storageOfBDD(bl.bdd), len(bl.memo)
			var stop atomic.Bool
			bl.bdd.stop = &stop
			stop.Store(true)
			switch operation {
			case "blast":
				if bl.blast(x) != nil {
					t.Fatal("cancelled cached blast returned bits")
				}
			case "equality":
				if _, exceeded := blastEqual(bl, &Function{Name: "cancelled"}, names, x, x, nil, 4, ""); !exceeded {
					t.Fatal("cancelled equality was accepted as proof")
				}
			case "theorem":
				if _, exceeded := decideBlasted(bl, nil, claim, names, evaluator); !exceeded {
					t.Fatal("cancelled theorem was accepted as a decision")
				}
			case "implication":
				if _, decided := impliesEqualUnder(bl, constTerm(1, 1), x, x, 4); decided {
					t.Fatal("cancelled implication was accepted as proof")
				}
			}
			if !bl.bdd.exceeded || storageOfBDD(bl.bdd) != before || len(bl.memo) != terms {
				t.Fatal("cancelled cached operation did not stop without growing storage")
			}
		})
	}
}

func TestBDDParallelProofSemantics(t *testing.T) {
	names, widths := []string{"x", "y", "z"}, map[string]int{"x": 4, "y": 4, "z": 4}
	x, y, z := paramTerm("x", 4), paramTerm("y", 4), paramTerm("z", 4)
	left := binaryTerm("and", x, binaryTerm("or", y, z))
	right := binaryTerm("or", binaryTerm("and", x, y), binaryTerm("and", x, z))
	for _, tc := range []struct {
		name string
		a, b *term
		want VerdictKind
	}{
		{"equal", left, right, VerdictProven},
		{"different", binaryTerm("xor", x, y), binaryTerm("or", x, y), VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			claim := cmpTerm("eq", tc.a, tc.b)
			evaluator := newTermEvaluator(claim)
			for iteration := 0; iteration < 12; iteration++ {
				for _, budget := range []int{1, 10000} {
					blasters := equalityBlasters(names, widths, tc.a, tc.b)
					for _, bl := range blasters {
						bl.withBudget(budget)
					}
					verdict, decided := raceBDDOrders(blasters, func(bl *blaster) (Verdict, bool) {
						return blastEqual(bl, &Function{Name: "parallel"}, names, tc.a, tc.b, nil, 4, "")
					})
					if decided != (budget > 1) || decided && verdict.Kind != tc.want {
						t.Fatalf("equality budget %d: decided=%v verdict=%v, want %v", budget, decided, verdict, tc.want)
					}
					for _, bl := range blasters {
						if bl.bdd.budget != budget {
							t.Fatal("race changed a node allowance")
						}
					}
					lowered := &loweredTheorem{claim: claim, names: names, widths: widths}
					blasters = lowered.blasters()
					for _, bl := range blasters {
						bl.withBudget(budget)
					}
					decision, decided := raceBDDOrders(blasters, func(bl *blaster) (Decision, bool) {
						return decideBlasted(bl, nil, claim, names, evaluator.fork())
					})
					want := DecisionProven
					if tc.want == VerdictMismatch {
						want = DecisionRefuted
					}
					if decided != (budget > 1) || decided && decision.Kind != want {
						t.Fatalf("theorem budget %d: decided=%v decision=%v, want %v", budget, decided, decision, want)
					}
				}
			}
		})
	}
}

func TestBDDOriginalNodeAllowances(t *testing.T) {
	if NodeBudget != 2000000 || blastNodeBudget != 2000000 {
		t.Fatal("default node allowance changed")
	}
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	if escalatedNodeBudget() != 16000000 {
		t.Fatal("high node allowance changed")
	}
}

func TestBDDInterruptionKeepsCNFDispatch(t *testing.T) {
	bl := newCNFBlaster([]string{"x"}, map[string]int{"x": 4})
	x := paramTerm("x", 4)
	bits := bl.blast(x)
	if len(bits) != 4 || bl.bdd != nil || bl.exceeded() {
		t.Fatal("CNF blasting unexpectedly depends on a BDD store")
	}
	cached := bl.blast(x)
	if len(cached) != len(bits) || &cached[0] != &bits[0] {
		t.Fatal("CNF cache behavior changed")
	}
	bl.cnf.exceeded = true
	if !bl.exceeded() || bl.blast(x) != nil {
		t.Fatal("CNF exhaustion no longer fails closed")
	}
}

func TestBDDOrderRaceRejectsCancelledResult(t *testing.T) {
	bl := newBlaster(nil, nil)
	if _, decided := raceBDDOrders([]*blaster{bl}, func(bl *blaster) (Verdict, bool) {
		bl.bdd.stop.Store(true)
		return Verdict{Kind: VerdictProven}, false
	}); decided {
		t.Fatal("a nominal result from an interrupted worker became a proof")
	}
}
