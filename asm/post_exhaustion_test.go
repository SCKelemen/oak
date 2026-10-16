package asm

import "testing"

// Source-only controls for the isolated post-exhaustion overlay. These use
// the real budget owner and checker, with no observer, source-file reads,
// scheduling override, or replacement decision. None may run in parallel.

func postExhaustionNoWidth(t *testing.T) func(string) int {
	t.Helper()
	return func(name string) int {
		t.Fatalf("exhausted wrapper or fast path reached width lookup for %q", name)
		return 8
	}
}

func TestPostExhaustionRefusesFreshAdmission(t *testing.T) {
	p := constTerm(1, 1)
	for _, remaining := range []int{0, -7} {
		for _, calls := range []int{17, implicationCallLimit - 1, implicationCallLimit} {
			for _, sides := range [][2]*term{
				{paramTerm("x", 8), paramTerm("y", 8)},
				{paramTerm("x", 8), paramTerm("x", 16)},
				{constTerm(0, 1), constTerm(1, 1)},
			} {
				key := decisionKey{p, sides[0], sides[1], 0}
				otherDepth := decisionKey{p, sides[0], sides[1], 1}
				keep := decisionResult{true, true}
				budget := &nodeBudget{remaining: remaining, calls: calls, decided: map[decisionKey]decisionResult{otherDepth: keep}}
				holds, decided := impliesEqualDepth(p, sides[0], sides[1], postExhaustionNoWidth(t), budget, 0)
				if holds || decided || budget.remaining != remaining || budget.calls != calls+1 {
					t.Fatalf("fresh admission changed refusal/accounting: initial=(%d,%d), result=(%v,%v), remaining=%d calls=%d", remaining, calls, holds, decided, budget.remaining, budget.calls)
				}
				if _, seen := budget.decided[key]; seen || len(budget.decided) != 1 || budget.decided[otherDepth] != keep {
					t.Fatal("fresh refusal poisoned the memo or reused a different depth")
				}
			}
		}
	}
}

func TestPostExhaustionPreservesEqualityAndMemo(t *testing.T) {
	p := paramTerm("premise", 1)
	x := paramTerm("x", 8)
	for _, remaining := range []int{0, -7} {
		for _, sides := range [][2]*term{
			{x, x},
			{constTerm(0, 1), constTerm(0, 1)}, // trap-domain zero
			{binaryTerm("add", paramTerm("index", 32), constTerm(1, 32)), binaryTerm("add", paramTerm("index", 32), constTerm(1, 32))},
		} {
			budget := &nodeBudget{remaining: remaining, calls: implicationCallLimit + 1}
			holds, decided := impliesEqualDepth(p, sides[0], sides[1], postExhaustionNoWidth(t), budget, 0)
			if !holds || !decided || budget.remaining != remaining || budget.calls != implicationCallLimit+1 || budget.decided != nil {
				t.Fatal("pointer/structural equality lost its pre-admission success")
			}
		}
		for _, want := range []decisionResult{{true, true}, {false, true}, {false, false}} {
			a, b := paramTerm("x", 8), paramTerm("y", 8)
			key := decisionKey{p, a, b, 0}
			budget := &nodeBudget{remaining: remaining, calls: implicationCallLimit + 1, decided: map[decisionKey]decisionResult{key: want}}
			holds, decided := impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), budget, 0)
			if (decisionResult{holds, decided}) != want || budget.remaining != remaining || budget.calls != implicationCallLimit+1 || len(budget.decided) != 1 || budget.decided[key] != want {
				t.Fatal("memo hit changed its exact Boolean pair, calls, or balance")
			}
		}
	}
}

func TestPostExhaustionPreservesMatchingEffects(t *testing.T) {
	for _, remaining := range []int{0, -7} {
		budget := &nodeBudget{remaining: remaining, calls: 17}
		decide := func(p, a, b *term) (bool, bool) {
			return impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), budget, 0)
		}
		makeLog := func(value string) []*spanWrite {
			return []*spanWrite{{memory: "loop1.cells"}, {index: paramTerm("index", 32), value: paramTerm(value, 8)}}
		}
		if !writeLogsEqualUnder(makeLog("value"), makeLog("value"), constTerm(1, 1), decide) || budget.remaining != remaining || budget.calls != 17 {
			t.Fatal("matching write effects lost zero-debit structural equality")
		}
		if writeLogsEqualUnder(makeLog("value"), makeLog("changed"), constTerm(1, 1), decide) || budget.remaining != remaining || budget.calls != 18 || len(budget.decided) != 0 {
			t.Fatal("an exhausted unequal write effect was accepted or charged nodes")
		}
	}
}

func TestPostExhaustionPositiveAdmissionStillOverdraws(t *testing.T) {
	p, a, b := constTerm(1, 1), paramTerm("x", 8), paramTerm("y", 8)
	for _, remaining := range []int{1, 2, 3} {
		budget := &nodeBudget{remaining: remaining, calls: 17}
		holds, decided := impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), budget, 0)
		if holds || decided || budget.remaining != remaining-3 || budget.calls != 18 || budget.decided != nil {
			t.Fatalf("positive admission changed its three-node debit: start=%d result=(%v,%v) remaining=%d calls=%d", remaining, holds, decided, budget.remaining, budget.calls)
		}
	}
	// The unchanged call ceiling still precedes DAG admission at positive balance.
	budget := &nodeBudget{remaining: 3, calls: implicationCallLimit}
	if holds, decided := impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), budget, 0); holds || decided || budget.remaining != 3 || budget.calls != implicationCallLimit+1 || budget.decided != nil {
		t.Fatal("call-limit refusal changed positive-balance admission")
	}
}

func TestPostExhaustionPreservesOversizedPenalty(t *testing.T) {
	// A wide, shallow DAG bounds stack depth while exceeding the distinct-node
	// limit. This is admission only; its uninterpreted operation is never run.
	args := make([]*term, implicationNodeLimit)
	for i := range args {
		args[i] = constTerm(uint64(i), 32)
	}
	a := &term{kind: termApply, width: 32, name: "oversized", args: args}
	for _, remaining := range []int{1, 0, -7} {
		budget := &nodeBudget{remaining: remaining}
		holds, decided := impliesEqualDepth(constTerm(1, 1), a, constTerm(0, 32), postExhaustionNoWidth(t), budget, 0)
		want := remaining
		if remaining > 0 {
			want -= blastNodeBudget
		}
		if holds || decided || budget.remaining != want || budget.calls != 1 || budget.decided != nil {
			t.Fatalf("oversized admission changed penalty/skip: start=%d remaining=%d want=%d calls=%d", remaining, budget.remaining, want, budget.calls)
		}
	}
}

func postExhaustionDistributivity(t *testing.T) (a, b *term, nodes int) {
	t.Helper()
	x, y, z := paramTerm("x", 2), paramTerm("y", 2), paramTerm("z", 2)
	a = canonical(binaryTerm("mul", x, binaryTerm("add", y, z)))
	b = canonical(binaryTerm("add", binaryTerm("mul", x, y), binaryTerm("mul", x, z)))
	nodes, exceeded := dagNodes(implicationNodeLimit, constTerm(1, 1), a, b)
	if exceeded || nodes != 9 || a.kind != termBinary || a.op != "mul" || b.kind != termBinary || b.op != "add" || equalTermsAtDeclaredWidths(a, b, func(string) int { return 2 }) || equalReductions(a, b) || hasLargeBranch(a) || hasLargeBranch(b) {
		t.Fatal("distributivity fixture no longer reaches the residual race with nine admission nodes")
	}
	return a, b, nodes
}

func TestPostExhaustionMainRaceSkippedAfterShortcut(t *testing.T) {
	a, b, nodes := postExhaustionDistributivity(t)
	widthOf := func(name string) int {
		if name == "irrelevant" {
			return 1
		}
		return 2
	}
	for _, loop := range []bool{false, true} {
		for _, initial := range []int{nodes, nodes - 1} {
			budget := &nodeBudget{remaining: initial, calls: 17, loop: loop}
			holds, decided := impliesEqualDepthUncached(paramTerm("irrelevant", 1), a, b, widthOf, budget, 0)
			// The no-premise child spends nine DAG nodes and refuses. The
			// single-conjunct premise has no relevant-premise retry; the
			// differing operation shapes cannot start congruence. The former
			// main BDD race would then spend one terminal node at this owner.
			if holds || decided || budget.remaining != initial-nodes || budget.calls != 18 || len(budget.decided) != 0 {
				t.Fatalf("loop=%v: exhausted shortcut leaked into main BDD work: initial=%d result=(%v,%v) remaining=%d calls=%d memo=%d", loop, initial, holds, decided, budget.remaining, budget.calls, len(budget.decided))
			}
		}
	}
}

func TestPostExhaustionBoundedTransferAndUnknownMemo(t *testing.T) {
	a, b, nodes := postExhaustionDistributivity(t)
	p := constTerm(1, 1)
	key := decisionKey{p, a, b, 0}
	keepKey := decisionKey{p, constTerm(0, 8), constTerm(1, 8), 1}
	keep := decisionResult{false, true}
	budget := &nodeBudget{remaining: 4096, calls: 17, loop: true, decided: map[decisionKey]decisionResult{keepKey: keep}}
	var child *nodeBudget
	holds, decided := budget.bounded(nodes+1, func(bounded *nodeBudget) (bool, bool) {
		child = bounded
		if child == budget || child.remaining != nodes+1 || child.calls != 17 || !child.optimistic || !child.loop || child.decided[keepKey] != keep {
			t.Fatal("bounded child did not inherit its exact effective allowance and state")
		}
		holds, decided := impliesEqualDepth(p, a, b, func(string) int { return 2 }, child, 0)
		if holds || decided || child.remaining != 0 || child.calls != 18 || len(child.decided) != 1 {
			t.Fatal("admitted one-node Unknown changed debit, calls, or optimistic memo authority")
		}
		// A second attempt at this same exhausted child spends one call,
		// no further DAG nodes, and does not borrow its parent's allowance.
		return impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), child, 0)
	})
	if holds || decided || child == nil || child.remaining != 0 || child.calls != 19 || budget.remaining != 4096-nodes-1 || budget.calls != 19 || len(budget.decided) != 1 || budget.decided[keepKey] != keep {
		t.Fatal("bounded attempt did not transfer its actual debit and calls exactly once")
	}
	if _, seen := budget.decided[key]; seen {
		t.Fatal("optimistic Unknown poisoned the shared memo")
	}
	// The parent's unused allowance can still decide the exact same key.
	holds, decided = impliesEqualDepth(p, a, b, func(string) int { return 2 }, budget, 0)
	if !holds || !decided || budget.calls != 20 || budget.remaining <= 0 || budget.decided[key] != (decisionResult{true, true}) || budget.decided[keepKey] != keep {
		t.Fatal("the exhausted child suppressed the parent's later actual decision")
	}
	// The same actually attempted Unknown retains ordinary memo authority
	// outside an optimistic child, including the exhausted repeat lookup.
	ordinary := &nodeBudget{remaining: nodes + 1}
	holds, decided = impliesEqualDepth(p, a, b, func(string) int { return 2 }, ordinary, 0)
	if holds || decided || ordinary.remaining != 0 || ordinary.calls != 1 || len(ordinary.decided) != 1 || ordinary.decided[key] != (decisionResult{false, false}) {
		t.Fatal("ordinary attempted Unknown lost its existing memo publication")
	}
	if holds, decided := impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), ordinary, 0); holds || decided || ordinary.remaining != 0 || ordinary.calls != 1 {
		t.Fatal("ordinary Unknown memo hit no longer precedes exhausted admission")
	}
}

func TestPostExhaustionKeepsAdmittedFinalNodeDecision(t *testing.T) {
	// False implies 0=1. No valuation can refute it and distinct constants
	// reach the main BDD; the complete diagram contains only its terminal.
	for _, loop := range []bool{false, true} {
		p, a, b := constTerm(0, 1), constTerm(0, 8), constTerm(1, 8)
		budget := &nodeBudget{remaining: 4, loop: loop}
		holds, decided := impliesEqualDepth(p, a, b, postExhaustionNoWidth(t), budget, 0)
		if !holds || !decided || budget.remaining != 0 || budget.calls != 1 || budget.decided[decisionKey{p, a, b, 0}] != (decisionResult{true, true}) {
			t.Fatal("a valid admitted BDD decision was discarded at exact depletion")
		}
	}
	if holds, decided := impliesEqualDepth(constTerm(0, 1), constTerm(0, 8), constTerm(1, 8), postExhaustionNoWidth(t), nil, 0); !holds || !decided {
		t.Fatal("nil-budget initialization lost an ordinary positive decision")
	}
	// Fixed-index element parameters agree with fixed witness memory during
	// valuation, but remain unconstrained in the BDD. One variable and its
	// terminal decide the real refutation using exactly two BDD nodes.
	p := constTerm(1, 1)
	a := selectTerm("postexhaustion", constTerm(0, 32), 1)
	b := constTerm(elementValue("postexhaustion", 0, 1), 1)
	budget := &nodeBudget{remaining: 5, loop: true}
	holds, decided := impliesEqualDepth(p, a, b, func(string) int { return 1 }, budget, 0)
	if holds || !decided || budget.remaining != 0 || budget.calls != 1 || budget.decided[decisionKey{p, a, b, 0}] != (decisionResult{false, true}) {
		t.Fatal("a valid admitted BDD refutation was discarded at exact depletion")
	}
}

func postExhaustionSplitFixture(t *testing.T) (p, a, b *term) {
	t.Helper()
	c, z := paramTerm("branch", 1), paramTerm("z", 8)
	x, y := paramTerm("x", 8), paramTerm("y", 8)
	for i := 0; i < 7; i++ {
		x, y = binaryTerm("mul", x, x), binaryTerm("mul", y, y)
	}
	a = canonical(binaryTerm("xor", iteTerm(c, x, y), z))
	b = canonical(iteTerm(c, binaryTerm("xor", x, z), binaryTerm("xor", y, z)))
	p = binaryTerm("and", paramTerm("irrelevant1", 1), paramTerm("irrelevant2", 1))
	nodes, exceeded := dagNodes(implicationNodeLimit, constTerm(1, 1), a, b)
	if exceeded || nodes != 24 || !hasLargeBranch(a) || !hasLargeBranch(b) || termSize(a, map[*term]int{})+termSize(b, map[*term]int{}) <= smallSides || equalTerms(a, b) || a.kind != termBinary || b.kind != termIte {
		t.Fatal("split fixture lost its 24-node DAG, large branch, or distinct shapes")
	}
	if relevant, dropped := relevantPremise(p, a, b); !dropped || relevant.kind != termConst || relevant.value != 1 {
		t.Fatal("split fixture no longer tries the weaker constant premise")
	}
	return p, a, b
}

func TestPostExhaustionRetainsFinalSplitSuccess(t *testing.T) {
	p, a, b := postExhaustionSplitFixture(t)
	widthOf := func(name string) int {
		if name == "branch" || name == "irrelevant1" || name == "irrelevant2" {
			return 1
		}
		return 8
	}
	for _, initial := range []int{24, 1} {
		budget := &nodeBudget{remaining: initial, calls: 17, loop: true}
		holds, decided := impliesEqualDepthUncached(p, a, b, widthOf, budget, 0)
		// Large sides bypass the small-side shortcut. The weaker-premise
		// child consumes exactly 24 DAG nodes, so one-sided arms refuses;
		// final split alone rewrites both arms into structural equalities.
		if !holds || !decided || budget.remaining != initial-24 || budget.calls != 18 || len(budget.decided) != 0 {
			t.Fatalf("shared final split lost its zero-node success: start=%d result=(%v,%v) remaining=%d calls=%d", initial, holds, decided, budget.remaining, budget.calls)
		}
	}
}

func TestPostExhaustionSplitFastPathsAndDepthLimit(t *testing.T) {
	p, a, b := postExhaustionSplitFixture(t)
	for _, remaining := range []int{0, -7} {
		budget := &nodeBudget{remaining: remaining, calls: 17}
		if holds, decided := splitDecide(p, a, b, postExhaustionNoWidth(t), budget, splitDepth-1); !holds || !decided || budget.remaining != remaining || budget.calls != 17 || budget.decided != nil {
			t.Fatal("final split's structurally equal children no longer succeed at exhausted balance")
		}
		if holds, decided := splitDecide(p, a, b, postExhaustionNoWidth(t), budget, splitDepth); holds || decided || budget.remaining != remaining || budget.calls != 17 || budget.decided != nil {
			t.Fatal("final split bypassed its depth limit")
		}
		c := paramTerm("fresh_branch", 1)
		left := iteTerm(c, paramTerm("x", 8), paramTerm("y", 8))
		right := iteTerm(c, paramTerm("changed", 8), paramTerm("y", 8))
		if holds, decided := splitDecide(constTerm(1, 1), left, right, postExhaustionNoWidth(t), budget, 0); holds || decided || budget.remaining != remaining || budget.calls != 18 || budget.decided != nil {
			t.Fatal("a fresh unequal split child was decided or charged nodes at exhaustion")
		}
	}
}

func TestPostExhaustionSplitMemoFastPath(t *testing.T) {
	c := paramTerm("memo_branch", 1)
	x, y, z := paramTerm("x", 8), paramTerm("y", 8), paramTerm("z", 8)
	a, b := iteTerm(c, x, z), iteTerm(c, y, z)
	// With an initial true premise, the first split child's premise is c
	// itself and its unchanged parameter sides preserve exact memo identity.
	key := decisionKey{c, x, y, 1}
	for _, remaining := range []int{0, -7} {
		for _, want := range []decisionResult{{true, true}, {false, true}, {false, false}} {
			budget := &nodeBudget{remaining: remaining, calls: 17, decided: map[decisionKey]decisionResult{key: want}}
			holds, decided := splitDecide(constTerm(1, 1), a, b, postExhaustionNoWidth(t), budget, 0)
			if (decisionResult{holds, decided}) != want || budget.remaining != remaining || budget.calls != 17 || len(budget.decided) != 1 || budget.decided[key] != want {
				t.Fatal("final split lost a memo fast path or changed its exact result")
			}
		}
	}
}
