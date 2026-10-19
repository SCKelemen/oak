package asm

import "github.com/SCKelemen/oak/internal/nativetiming"

// Direct private entries preserve their old unobserved route. Recursive calls
// under a classified wrapper explicitly retain its observation handle. No
// observation is stored in a proof budget, immutable session, or term DAG.

func (session *verificationSession) impliesEqualDepth(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualDepthObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) impliesEqualDepthUncached(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualDepthUncachedObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) splitDecide(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.splitDecideObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) splitDecideOn(premise, a, b, cond *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.splitDecideOnObserved(premise, a, b, cond, widthOf, budget, depth, nil)
}

func (session *verificationSession) impliesEqualOneSidedArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualOneSidedArmsObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) impliesEqualByArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualByArmsObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) impliesEqualCongruent(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualCongruentObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) impliesEqualArms(premise, a, b *term, widthOf func(string) int, budget *nodeBudget, depth int) (holds bool, decided bool) {
	return session.impliesEqualArmsObserved(premise, a, b, widthOf, budget, depth, nil)
}

func (session *verificationSession) premiseUnderItself(premise *term) *term {
	return session.premiseUnderItselfObserved(premise, nil)
}

// These adapters bracket only the listed serial coordinator boundaries. Their
// defers include the original callee's cleanup and propagate panics unchanged.
// Nil handles keep the same solver calls, argument evaluation order and budgets.
func implicationDAGNodes(timing *nativetiming.ImplicationObservation, limit int, roots ...*term) (int, bool) {
	stage := timing.Push(nativetiming.StageDAGAdmission)
	defer stage.End()
	return dagNodes(limit, roots...)
}

func implicationCanonical(timing *nativetiming.ImplicationObservation, t *term) *term {
	stage := timing.Push(nativetiming.StageCanonicalPass)
	defer stage.End()
	return canonical(t)
}

func implicationPruneUnder(timing *nativetiming.ImplicationObservation, premise *term, terms []*term, widthOf func(string) int) []*term {
	stage := timing.Push(nativetiming.StageStandalonePruning)
	defer stage.End()
	return pruneUnder(premise, terms, widthOf)
}

func implicationBDDOrders(timing *nativetiming.ImplicationObservation, blasters []*blaster, run func(*blaster) (bool, bool)) (bool, bool) {
	stage := timing.Push(nativetiming.StageBDDJoined)
	defer stage.End()
	return raceBDDOrders(blasters, run)
}

func implicationBounded(timing *nativetiming.ImplicationObservation, budget *nodeBudget, limit int, attempt func(*nodeBudget) (bool, bool)) (bool, bool) {
	stage := timing.Push(nativetiming.StageRecursiveScheduling)
	defer stage.End()
	return budget.bounded(limit, attempt)
}
