package asm

// A termEvaluator evaluates a theorem's terms over many inputs without
// allocating per input (docs/notes/formal-methods-performance-2026-09.md,
// item 3): it numbers every subterm of its roots once, and remembers
// values in slices indexed by that number, a generation stamp saying
// which evaluation a value belongs to. The map memo it replaces cost one
// allocation and a rehash per witness input.
type termEvaluator struct {
	terms []*term
	value []uint64
	stamp []uint32
	gen   uint32
}

func newTermEvaluator(roots ...*term) *termEvaluator {
	ev := &termEvaluator{}
	for _, root := range roots {
		ev.number(root)
	}
	ev.value = make([]uint64, len(ev.terms)+1)
	ev.stamp = make([]uint32, len(ev.terms)+1)
	return ev
}

// numbered reports whether t already carries this evaluator's id.
func (ev *termEvaluator) numbered(t *term) bool {
	return t.id > 0 && int(t.id) <= len(ev.terms) && ev.terms[t.id-1] == t
}

func (ev *termEvaluator) number(t *term) {
	// Constants are not numbered: they cost nothing to evaluate, and a
	// constant term may be shared between theorems (trapPath), which
	// theorems decided in parallel must not write to.
	if t == nil || t.kind == termConst || ev.numbered(t) {
		return
	}
	ev.terms = append(ev.terms, t)
	t.id = int32(len(ev.terms))
	ev.number(t.left)
	ev.number(t.right)
	ev.number(t.cond)
}

// evaluate is one evaluation of a root over env.
func (ev *termEvaluator) evaluate(t *term, env map[string]uint64) uint64 {
	ev.gen++
	if ev.gen == 0 {
		// The stamps wrapped: clear them so no stale value reads as current.
		for i := range ev.stamp {
			ev.stamp[i] = 0
		}
		ev.gen = 1
	}
	return ev.eval(t, env)
}

func (ev *termEvaluator) eval(t *term, env map[string]uint64) uint64 {
	if t.kind == termConst || !ev.numbered(t) {
		// A term outside the numbered roots: evaluated without the memo.
		return t.evalUncached(env, ev)
	}
	id := t.id
	if ev.stamp[id] == ev.gen {
		return ev.value[id]
	}
	value := t.evalUncached(env, ev)
	ev.stamp[id] = ev.gen
	ev.value[id] = value
	return value
}
