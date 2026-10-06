package asm

import (
	"strings"
	"testing"
)

func TestApplicationCongruence(t *testing.T) {
	x := paramTerm("x", 32)
	y := paramTerm("y", 32)
	left := applyTerm("Bits.mix/result0", 32, x, constTerm(7, 8))
	right := applyTerm("Bits.mix/result0", 32, y, constTerm(7, 8))
	premise := cmpTerm("eq", x, y)
	widthOf := func(string) int { return 32 }

	if holds, decided := impliesEqual(premise, left, right, widthOf); !decided || !holds {
		t.Fatalf("congruent applications were not proved equal: holds=%v decided=%v", holds, decided)
	}
	changed := binaryTerm("xor", left, constTerm(1, 32))
	if holds, decided := impliesEqual(constTerm(1, 1), left, changed, widthOf); !decided || holds {
		t.Fatalf("a changed application result was not refuted: holds=%v decided=%v", holds, decided)
	}
}

func TestApplicationAckermannConstraint(t *testing.T) {
	x := paramTerm("x", 8)
	y := paramTerm("y", 8)
	left := applyTerm("f", 8, x)
	right := applyTerm("f", 8, y)
	bl := newBlaster([]string{"x", "y"}, map[string]int{"x": 8, "y": 8})
	premise := bl.blast(cmpTerm("eq", x, y))[0]
	lbits, rbits := bl.blast(left), bl.blast(right)
	different := bddFalse
	for i := range lbits {
		different = bl.apply(opOr, different, bl.apply(opXor, lbits[i], rbits[i]))
	}
	bad := bl.apply(opAnd, premise, bl.apply(opAnd, bl.consistency(), different))
	if bad != bddFalse || bl.exceeded() {
		t.Fatalf("congruence left a model with equal arguments and different results: node=%d exceeded=%v", bad, bl.exceeded())
	}
}

func TestApplicationSignatureIsPartOfIdentity(t *testing.T) {
	x32 := paramTerm("x", 32)
	x16 := paramTerm("x", 16)
	a := applyTerm("callee", 32, x32)
	b := applyTerm("callee.other", 32, x32)
	c := applyTerm("callee", 64, x32)
	d := applyTerm("callee", 32, x16)

	for name, other := range map[string]*term{"name": b, "result width": c, "argument width": d} {
		if equalTerms(a, other) {
			t.Fatalf("application with a different %s compared structurally equal", name)
		}
		if applicationSpan(a.name, a.width, a.args) == applicationSpan(other.name, other.width, other.args) {
			t.Fatalf("application with a different %s shared an abstraction namespace", name)
		}
	}
	if got := applyTerm("constant", 8).eval(nil); got != applyTerm("constant", 8).eval(nil) {
		t.Fatalf("nullary application did not have one stable value: %#x", got)
	}
}

func TestApplicationWitnessAndTraversal(t *testing.T) {
	x := paramTerm("x", 32)
	y := paramTerm("y", 16)
	inner := applyTerm("inner", 16, y)
	root := applyTerm("outer", 32, x, inner)
	env := map[string]uint64{"x": 3, "y": 5}

	first := root.eval(env)
	if again := root.eval(env); again != first {
		t.Fatalf("application witness is not deterministic: %#x then %#x", first, again)
	}
	for name, changed := range map[string]map[string]uint64{
		"first argument":  {"x": 4, "y": 5},
		"nested argument": {"x": 3, "y": 6},
	} {
		if got := root.eval(changed); got == first {
			t.Fatalf("changing the %s did not change the witness value %#x", name, got)
		}
	}

	params := map[string]bool{}
	collectParams(root, params)
	if !params["x"] || !params["y"] || len(params) != 2 {
		t.Fatalf("application parameters = %v, want x and y", params)
	}
	z := paramTerm("z", 16)
	rewritten := substitute(root, map[string]*term{"x": constTerm(9, 32), "y": z})
	if rewritten.kind != termApply || rewritten.args[0].kind != termConst || rewritten.args[0].value != 9 {
		t.Fatalf("outer application was not substituted: %s", rewritten)
	}
	if got := rewritten.args[1]; got.kind != termApply || len(got.args) != 1 || got.args[0] != z {
		t.Fatalf("nested application was not substituted: %s", rewritten)
	}

	evaluator := newTermEvaluator(root)
	if got := evaluator.evaluate(root, env); got != first {
		t.Fatalf("numbered evaluation = %#x, direct evaluation = %#x", got, first)
	}
	direct := applicationValue("inner", 16, []uint64{5}, []int{16})
	if got := inner.eval(env); got != direct {
		t.Fatalf("application witness = %#x, direct interpretation = %#x", got, direct)
	}
}

func TestApplicationOwnsArgumentList(t *testing.T) {
	x := paramTerm("x", 8)
	y := paramTerm("y", 8)
	args := []*term{x}
	application := applyTerm("f", 8, args...)
	args[0] = y
	if application.args[0] != x {
		t.Fatal("mutating the constructor's argument slice changed the application")
	}
}

func TestApplicationTraversesMemoryAndFailsClosedAtCertificateBoundaries(t *testing.T) {
	index := paramTerm("i", 32)
	read := selectTerm("memory", index, 32)
	root := applyTerm("reader", 32, read)
	if !termContainsSelect(root) || !readsMemory(root) {
		t.Fatal("a memory read inside an application was hidden from memory analysis")
	}
	if !hasUninterpreted(root) {
		t.Fatal("an application was not classified as uninterpreted")
	}
	if reason := nativeCertificateTermReason(root, map[string]int{"i": 32}); !strings.Contains(reason, "outside pure scalar bit operations") {
		t.Fatalf("native certificate accepted an application: %q", reason)
	}
	if !theoremHasGeneralApplication(root, nil) {
		t.Fatal("Oak solver export did not detect an unsupported application")
	}
}

func TestApplicationDeclaredWidthEqualityChecksArguments(t *testing.T) {
	x := paramTerm("x", 32)
	y := paramTerm("y", 32)
	a := applyTerm("f", 32, x)
	b := applyTerm("f", 32, y)
	if equalTermsAtDeclaredWidths(a, b, func(string) int { return 32 }) {
		t.Fatal("applications with different arguments compared equal at declared widths")
	}
}

func TestApplicationEvidenceCannotRefuteTheorem(t *testing.T) {
	x := paramTerm("x", 8)
	application := applyTerm("call:callee:result", 8, x)
	atZero := application.eval(map[string]uint64{"x": 0})
	names := []string{"x"}
	widths := map[string]int{"x": 8}

	tests := []struct {
		name  string
		claim *term
		traps []*term
	}{
		{
			name:  "claim",
			claim: cmpTerm("eq", application, constTerm(atZero^1, 8)),
		},
		{
			name:  "trap",
			claim: constTerm(1, 1),
			traps: []*term{cmpTerm("eq", application, constTerm(atZero, 8))},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			lowered := &loweredTheorem{claim: test.claim, traps: test.traps, names: names, widths: widths}
			if decision, refuted := lowered.witnessRefutation(); refuted || decision.Kind == DecisionRefuted {
				t.Fatalf("the evidence interpretation refuted the theorem during witness evaluation: %#v", decision)
			}

			bl := newBlaster(names, widths)
			evaluator := newTermEvaluator(append([]*term{test.claim}, test.traps...)...)
			decision, exceeded := decideBlasted(bl, test.traps, test.claim, names, evaluator)
			if exceeded || decision.Kind != DecisionUndecided {
				t.Fatalf("application-dependent diagrams = %#v, exceeded=%v; want undecided", decision, exceeded)
			}
		})
	}
}
