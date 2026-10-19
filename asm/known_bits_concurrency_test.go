package asm

import (
	"sync"
	"testing"
)

// The variable-order proof workers share terms, including cold subgraphs.
// Build raw nodes so constructors cannot warm any analysis before the race.
func coldKnownBitsDAG() *term {
	x := &term{kind: termParam, name: "x", width: 64}
	n := &term{kind: termBinary, op: "and", width: 64, left: x, right: constTerm(255, 64)}
	n = &term{kind: termBinary, op: "or", width: 64, left: n, right: constTerm(0x500, 64)}
	for range 64 {
		// Both edges share their child: analysis must memoize the DAG,
		// rather than walking an exponentially large unfolded tree.
		n = &term{kind: termBinary, op: "or", width: 64, left: n, right: n}
	}
	return n
}

func TestKnownBitsConcurrentColdDAG(t *testing.T) {
	wantValue, wantKnown := knownBits(coldKnownBitsDAG())
	if wantValue != 0x500 || wantKnown != ^uint64(255) {
		t.Fatalf("serial known bits = (%#x, %#x)", wantValue, wantKnown)
	}
	for range 16 {
		root := coldKnownBitsDAG()
		start := make(chan struct{})
		var workers sync.WaitGroup
		for range 8 {
			workers.Go(func() {
				<-start
				value, known := knownBits(root)
				if value != wantValue || known != wantKnown {
					t.Errorf("concurrent known bits = (%#x, %#x), want (%#x, %#x)", value, known, wantValue, wantKnown)
				}
			})
		}
		close(start)
		workers.Wait()
	}
}

// This is the failing call path in the native Stage2 regression:
// independent blasters reach index bounds on the same shared term DAG.
func TestConsistencyConcurrentColdIndexBounds(t *testing.T) {
	for range 32 {
		base, x := paramTerm("base", 32), paramTerm("x", 32)
		low := &term{kind: termBinary, op: "and", width: 32, left: x, right: constTerm(255, 32)}
		high := &term{kind: termBinary, op: "add", width: 32, left: low, right: constTerm(256, 32)}
		left := selectTerm("mem", &term{kind: termBinary, op: "add", width: 32, left: base, right: low}, 8)
		right := selectTerm("mem", &term{kind: termBinary, op: "add", width: 32, left: base, right: high}, 8)
		start := make(chan struct{})
		var workers sync.WaitGroup
		for range 8 {
			workers.Go(func() {
				bl := newBlaster([]string{"base", "x"}, map[string]int{"base": 32, "x": 32})
				<-start
				bl.blast(left)
				bl.blast(right)
				if got := bl.consistency(); got != bddTrue || bl.exceeded() {
					t.Errorf("disjoint indices need no consistency constraint: result %d, exceeded %v", got, bl.exceeded())
				}
			})
		}
		close(start)
		workers.Wait()
	}
}

func TestKnownBitsRewrittenTerms(t *testing.T) {
	x := paramTerm("x", 8)
	original := &term{kind: termBinary, op: "and", width: 8, left: x, right: constTerm(15, 8)}
	memo := knownBitsMemo{}
	check := func(n *term, wantValue, wantKnown uint64) {
		t.Helper()
		value, known := memo.bits(n)
		if value != wantValue || known != wantKnown {
			t.Fatalf("known bits of %s = (%#x, %#x), want (%#x, %#x)", n, value, known, wantValue, wantKnown)
		}
	}
	check(original, 0, 0xf0)
	// A structural copy has a new identity and must not inherit the old
	// result, even when queried through the very same analysis cache.
	copied := *original
	copied.left = constTerm(10, 8)
	check(&copied, 10, 0xff)
	// Exercise the actual rewrite path too, after warming the source DAG.
	sigma := map[string]*term{"x": constTerm(10, 8)}
	rewritten := substituteMemo(original, sigma, map[*term]*term{})
	check(rewritten, 10, 0xff)
	check(original, 0, 0xf0)

	// Float construction and rewriting must still fold exactly the same
	// fully known input (the IEEE binary32 representation of 10).
	for _, folded := range []*term{
		floatTerm("ucvtf", 32, rewritten),
		substituteMemo(floatTerm("ucvtf", 32, original), sigma, map[*term]*term{}),
	} {
		if folded.kind != termConst || folded.value != 0x41200000 || folded.width != 32 {
			t.Fatalf("known float operand did not fold to binary32 10: %s", folded)
		}
	}
}

func TestKnownBitsAnalysisMemo(t *testing.T) {
	root := coldKnownBitsDAG()
	memo := knownBitsMemo{}
	memo.bits(root)
	// Two recursive operand nodes plus 64 shared OR nodes; trivial leaves
	// do not need memo entries. The memo is kept
	// for the entire analysis, including repeated and width-adapted queries.
	if len(memo) != 66 {
		t.Fatalf("memo contains %d nodes, want 66", len(memo))
	}
	for _, width := range []int{8, 32, 64} {
		value, known := memo.adapt(root, width)
		if value != 0x500&mask(width) || known != mask(width)&^255 {
			t.Fatalf("known bits at width %d = (%#x, %#x)", width, value, known)
		}
	}
	if len(memo) != 66 {
		t.Fatalf("repeated queries changed the memo to %d nodes", len(memo))
	}
}
