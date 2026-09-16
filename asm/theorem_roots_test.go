package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func requireTheoremRoot(t *testing.T, got, want *term) {
	t.Helper()
	if !equalTerms(got, want) {
		t.Fatalf("root = %s, want %s", got, want)
	}
}

func requireTheoremTrapRoots(t *testing.T, got, want []*term) {
	t.Helper()
	if len(got) != len(want) {
		t.Fatalf("trap root count = %d, want %d", len(got), len(want))
	}
	for i := range want {
		if !equalTerms(got[i], want[i]) {
			t.Fatalf("trap root %d = %s, want %s", i, got[i], want[i])
		}
	}
}

func failedTheoremCondition(cond *term) *term {
	return binaryTerm("xor", truncate(cond, 1), constTerm(1, 1))
}

func TestAssembleTheoremRootsPreservesSuppliedOrder(t *testing.T) {
	body := paramTerm("body", 8)
	first := paramTerm("first", 8)
	second := paramTerm("second", 1)
	raw := []*term{first, second, first}

	claim, traps := assembleTheoremRoots(constTerm(1, 1), body, raw)
	requireTheoremRoot(t, claim, truncate(body, 1))
	requireTheoremTrapRoots(t, traps, []*term{truncate(first, 1), second, truncate(first, 1)})

	// The projection owns its root list: later caller mutation cannot reorder
	// or replace the supplied encounter sequence.
	raw[0] = second
	requireTheoremTrapRoots(t, traps, []*term{truncate(first, 1), second, truncate(first, 1)})
}

func TestAssembleTheoremRootsGuardsClaimAndTraps(t *testing.T) {
	assume := paramTerm("assume", 1)
	body := paramTerm("body", 8)
	first := paramTerm("first", 8)
	second := paramTerm("second", 1)

	claim, traps := assembleTheoremRoots(assume, body, []*term{first, second})
	notAssume := binaryTerm("xor", assume, constTerm(1, 1))
	requireTheoremRoot(t, claim, binaryTerm("or", notAssume, truncate(body, 1)))
	requireTheoremTrapRoots(t, traps, []*term{
		binaryTerm("and", assume, truncate(first, 1)),
		binaryTerm("and", assume, second),
	})

	for assumeValue := uint64(0); assumeValue <= 1; assumeValue++ {
		for bodyValue := uint64(0); bodyValue <= 1; bodyValue++ {
			env := map[string]uint64{"assume": assumeValue, "body": bodyValue, "first": 1, "second": 1}
			wantClaim := (assumeValue ^ 1) | bodyValue
			if got := claim.eval(env); got != wantClaim {
				t.Fatalf("claim(%d,%d) = %d, want %d", assumeValue, bodyValue, got, wantClaim)
			}
			for i, trap := range traps {
				if got := trap.eval(env); got != assumeValue {
					t.Fatalf("trap %d under assumption %d = %d, want %d", i, assumeValue, got, assumeValue)
				}
			}
		}
	}
}

func parseTheoremRootProgram(t *testing.T, source, theorem string) (*ast.FunctionStatement, map[string]*ast.FunctionStatement) {
	t.Helper()
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parse theorem-root fixture: %v", errs)
	}
	functions := map[string]*ast.FunctionStatement{}
	for _, statement := range program.Statements {
		if fn, ok := statement.(*ast.FunctionStatement); ok && fn.Name != nil {
			functions[fn.Name.Value] = fn
		}
	}
	sig := functions[theorem]
	if sig == nil {
		t.Fatalf("theorem-root fixture has no function %q", theorem)
	}
	return sig, functions
}

func lowerTheoremRootFixture(t *testing.T, source string) *loweredTheorem {
	t.Helper()
	sig, functions := parseTheoremRootProgram(t, source, "law")
	lowered, undecided := lowerTheorem(sig, functions, nil, Declarations{})
	if undecided != nil {
		t.Fatalf("lower theorem-root fixture: %s", undecided.Message)
	}
	return lowered
}

func TestLowerTheoremSequentialTrapEncounterOrder(t *testing.T) {
	lowered := lowerTheoremRootFixture(t, `
law: (a, b, c: Bool) -> Bool = {
  assert(a)
  assert(b)
  assert(c)
  true
}
`)
	requireTheoremRoot(t, lowered.claim, constTerm(1, 1))
	requireTheoremTrapRoots(t, lowered.traps, []*term{
		failedTheoremCondition(paramTerm("a", 1)),
		failedTheoremCondition(paramTerm("b", 1)),
		failedTheoremCondition(paramTerm("c", 1)),
	})
}

func TestLowerTheoremBranchTrapPathPolarity(t *testing.T) {
	lowered := lowerTheoremRootFixture(t, `
law: (gate, yes, no: Bool) -> Bool = {
  gate ? {
    assert(yes)
  } | {
    assert(no)
  }
  true
}
`)
	gate := paramTerm("gate", 1)
	requireTheoremTrapRoots(t, lowered.traps, []*term{
		binaryTerm("and", gate, failedTheoremCondition(paramTerm("yes", 1))),
		binaryTerm("and", failedTheoremCondition(gate), failedTheoremCondition(paramTerm("no", 1))),
	})
}

func TestLowerTheoremInlineCallTrapPlacement(t *testing.T) {
	lowered := lowerTheoremRootFixture(t, `
check: (value: Bool) -> () = {
  assert(value)
}

law: (before, inside, after: Bool) -> Bool = {
  assert(before)
  check(inside)
  assert(after)
  true
}
`)
	requireTheoremTrapRoots(t, lowered.traps, []*term{
		failedTheoremCondition(paramTerm("before", 1)),
		failedTheoremCondition(paramTerm("inside", 1)),
		failedTheoremCondition(paramTerm("after", 1)),
	})
}

func TestLowerTheoremCountedLoopTrapMultiplicityAndOrder(t *testing.T) {
	lowered := lowerTheoremRootFixture(t, `
law: (first, second: Bool) -> Bool = {
  i: u8 = u8(0)
  while i < u8(2) {
    assert(first)
    assert(second)
    i = i + u8(1)
  }
  true
}
`)
	first := failedTheoremCondition(paramTerm("first", 1))
	second := failedTheoremCondition(paramTerm("second", 1))
	requireTheoremTrapRoots(t, lowered.traps, []*term{first, second, first, second})
}
