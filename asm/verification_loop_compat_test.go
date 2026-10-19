package asm

import "github.com/SCKelemen/oak/ast"

// Legacy private test entry points use default options unless their existing
// budget already belongs to an explicit verification session. Production code
// calls the session methods directly.
func verifyLoops(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, lowering *oakLowering, asmTerms, oakTerms []*term, width int) Verdict {
	session := &verificationSession{}
	return session.verifyLoops(fn, sig, oakBody, exec, lowering, asmTerms, oakTerms, width)
}

func verifyLoopsWith(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, lowering *oakLowering, asmTerms, oakTerms []*term, width int, abstractReach bool) Verdict {
	session := &verificationSession{}
	return session.verifyLoopsWith(fn, sig, oakBody, exec, lowering, asmTerms, oakTerms, width, abstractReach)
}

func headersEqual(hr, hx *term, widthOf func(string) int) bool {
	session := &verificationSession{}
	return session.headersEqual(hr, hx, widthOf)
}

func impliesEqual(premise, a, b *term, widthOf func(string) int) (holds bool, decided bool) {
	session := &verificationSession{}
	return session.impliesEqual(premise, a, b, widthOf)
}

func impliesEqualWithin(premise, a, b *term, widthOf func(string) int, budget *nodeBudget) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualWithin(premise, a, b, widthOf, budget)
}

func impliesEqualDepth(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualDepth(premise, a, b, widthOf, budget, depth)
}

func impliesEqualDepthUncached(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualDepthUncached(premise, a, b, widthOf, budget, depth)
}

func impliesFiniteConditionalEqual(premise, a, b *term, widthOf func(string) int, budget *nodeBudget) (holds, decided, applicable bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesFiniteConditionalEqual(premise, a, b, widthOf, budget)
}

func splitDecide(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.splitDecide(premise, a, b, widthOf, budget, depth)
}

func splitDecideOn(premise, a, b, cond *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.splitDecideOn(premise, a, b, cond, widthOf, budget, depth)
}

func premiseUnderItself(premise *term) *term {
	session := &verificationSession{}
	return session.premiseUnderItself(premise)
}

func impliesEqualOneSidedArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualOneSidedArms(premise, a, b, widthOf, budget, depth)
}

func impliesEqualByArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualByArms(premise, a, b, widthOf, budget, depth)
}

func impliesEqualCongruent(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualCongruent(premise, a, b, widthOf, budget, depth)
}

func impliesEqualArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	session := &verificationSession{}
	if budget != nil {
		session = budget.session
	}
	return session.impliesEqualArms(premise, a, b, widthOf, budget, depth)
}
