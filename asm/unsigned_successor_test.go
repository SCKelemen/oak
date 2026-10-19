package asm

import "testing"

func unsignedSuccessorExample(width int) (premise, goal, truth *term) {
	k := &term{kind: termParam, width: width, declared: width, name: "k"}
	bound := &term{kind: termParam, width: width, declared: width, name: "bound"}
	guard := &term{kind: termCmp, width: 1, op: "lo", left: k, right: bound}
	weak := &term{kind: termCmp, width: 1, op: "ls", left: k, right: bound}
	premise = &term{kind: termBinary, width: 1, op: "and", left: weak, right: guard}
	step := &term{kind: termBinary, width: width, op: "add", left: k, right: constTerm(1, width)}
	goal = &term{kind: termCmp, width: width, op: "ls", left: step, right: bound}
	return premise, goal, constTerm(1, 1)
}

func TestUnsignedSuccessorIdentityControls(t *testing.T) {
	for _, width := range []int{1, 2, 8, 16, 32, 64} {
		p, a, b := unsignedSuccessorExample(width)
		if !impliesUnsignedSuccessor(p, a, b) {
			t.Fatalf("same-width identity case refused at width %d", width)
		}
		if !impliesUnsignedSuccessor(p.right, a, b) {
			t.Fatalf("direct strict guard refused at width %d", width)
		}
		a.width = 1
		if !impliesUnsignedSuccessor(p, a, b) {
			t.Fatalf("one-bit comparison result refused at width %d", width)
		}
	}
	mutations := []struct {
		name string
		apply func(p, a, b *term)
	}{
		{"signed goal", func(p, a, b *term) { a.op = "le" }},
		{"signed guard", func(p, a, b *term) { p.right.op = "lt" }},
		{"prefixed guard", func(p, a, b *term) { p.right.op = "add:lo" }},
		{"weak guard only", func(p, a, b *term) { p.right.op = "ls" }},
		{"disjunction", func(p, a, b *term) { p.op = "or" }},
		{"wide conjunction", func(p, a, b *term) { p.width = 32 }},
		{"wide guard", func(p, a, b *term) { p.right.width = 32 }},
		{"changed bound", func(p, a, b *term) { a.right = binaryTerm("add", a.right, constTerm(1, 32)) }},
		{"same-name bound clone", func(p, a, b *term) { clone := *a.right; a.right = &clone }},
		{"same-name counter clone", func(p, a, b *term) { clone := *a.left.left; a.left.left = &clone }},
		{"changed bound width", func(p, a, b *term) { a.right.width = 64 }},
		{"narrow parameter declaration", func(p, a, b *term) { a.left.left.declared = 16 }},
		{"wide parameter declaration", func(p, a, b *term) { a.left.left.declared = 64 }},
		{"different step width", func(p, a, b *term) { a.left.width = 16 }},
		{"different one width", func(p, a, b *term) { a.left.right.width = 16 }},
		{"nonunit increment", func(p, a, b *term) { a.left.right.value = 2 }},
		{"subtraction", func(p, a, b *term) { a.left.op = "sub" }},
		{"zero width", func(p, a, b *term) { a.left.width = 0 }},
		{"oversize width", func(p, a, b *term) { a.left.width = 65 }},
		{"unsupported result width", func(p, a, b *term) { a.width = 16 }},
		{"false equality target", func(p, a, b *term) { b.value = 0 }},
		{"wide equality target", func(p, a, b *term) { b.width = 32 }},
		{"missing increment", func(p, a, b *term) { a.left.right = nil }},
		{"missing counter", func(p, a, b *term) { a.left.left = nil }},
		{"missing goal bound", func(p, a, b *term) { a.right = nil }},
		{"missing guard side", func(p, a, b *term) { p.right.left = nil }},
		{"missing conjunction side", func(p, a, b *term) { p.left = nil }},
		{"extra goal condition", func(p, a, b *term) { a.cond = b }},
		{"extra step argument", func(p, a, b *term) { a.left.args = []*term{b} }},
		{"extra constant child", func(p, a, b *term) { a.left.right.left = b }},
		{"conjunction cycle", func(p, a, b *term) { p.left = p }},
		{"shared conjunction leaf", func(p, a, b *term) { p.left = p.right }},
	}
	for _, tt := range mutations {
		t.Run(tt.name, func(t *testing.T) {
			p, a, b := unsignedSuccessorExample(32)
			tt.apply(p, a, b)
			if impliesUnsignedSuccessor(p, a, b) {
				t.Fatal("unsupported or malformed matcher spine was accepted")
			}
		})
	}
	p, a, b := unsignedSuccessorExample(32)
	if impliesUnsignedSuccessor(nil, a, b) || impliesUnsignedSuccessor(p, nil, b) || impliesUnsignedSuccessor(p, a, nil) {
		t.Fatal("nil root accepted")
	}
	for i := 0; i < unsignedSuccessorPremiseLimit; i++ {
		p = &term{kind: termBinary, width: 1, op: "and", left: constTerm(1, 1), right: p}
	}
	if impliesUnsignedSuccessor(p, a, b) {
		t.Fatal("premise walk cap was bypassed")
	}
}

// Evaluate the source terms with the existing evaluator, independently of the
// matcher. In particular, maximum-value counters never satisfy the strict guard.
func TestUnsignedSuccessorExhaustiveSmallWidths(t *testing.T) {
	for width := 1; width <= 6; width++ {
		p, a, b := unsignedSuccessorExample(width)
		if !impliesUnsignedSuccessor(p, a, b) {
			t.Fatal("test does not exercise an accepted matcher shape")
		}
		for k := uint64(0); k <= mask(width); k++ {
			for bound := uint64(0); bound <= mask(width); bound++ {
				env := map[string]uint64{"k": k, "bound": bound}
				m := mapMemo{}
				if m.eval(p, env) != 0 && m.eval(a, env) != m.eval(b, env) {
					t.Fatalf("counterexample at width %d, k=%d, bound=%d", width, k, bound)
				}
			}
		}
	}
	for _, width := range []int{32, 64} {
		p, a, _ := unsignedSuccessorExample(width)
		for _, env := range []map[string]uint64{
			{"k": mask(width) - 1, "bound": mask(width)},
			{"k": mask(width), "bound": mask(width)},
			{"k": mask(width), "bound": 0},
		} {
			m := mapMemo{}
			pv, av := m.eval(p, env), m.eval(a, env)
			if env["k"] == mask(width) && pv != 0 {
				t.Fatal("maximum counter unexpectedly satisfies the strict guard")
			}
			if pv != 0 && av != 1 {
				t.Fatal("word-boundary successor failed")
			}
		}
	}
}

func TestUnsignedSuccessorBudgetHook(t *testing.T) {
	p, a, b := unsignedSuccessorExample(32)
	nodes, exceeded := dagNodes(implicationNodeLimit, p, a, b)
	if exceeded {
		t.Fatal("small control exceeded admission")
	}
	budget := &nodeBudget{remaining: nodes + 1, loop: true}
	holds, decided := impliesEqualDepth(p, a, b, func(string) int { return 32 }, budget, 0)
	if !holds || !decided || budget.calls != 1 || budget.remaining != 1 {
		t.Fatalf("hook failed or changed accounting: holds=%v decided=%v calls=%d remaining=%d", holds, decided, budget.calls, budget.remaining)
	}
	if got, ok := budget.decided[decisionKey{p, a, b, 0}]; !ok || !got.holds || !got.decided {
		t.Fatal("successful shortcut did not use normal memo publication")
	}
	budget = &nodeBudget{remaining: nodes, loop: true}
	if holds, decided := impliesEqualDepth(p, a, b, func(string) int { return 32 }, budget, 0); holds || decided {
		t.Fatal("shortcut bypassed existing remaining-budget refusal")
	}
}
