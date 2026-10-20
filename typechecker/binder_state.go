package typechecker

// Persistent binder state is committed only after the enclosing expression
// succeeds. The equation solver in unification.go never commits these maps.

func (tc *TypeChecker) beginMonomorphicTransaction() {
	tc.monomorphicTransactions = append(tc.monomorphicTransactions, nil)
}

func (tc *TypeChecker) stageMonomorphicBindings(bindings Substitution) {
	if len(bindings) == 0 {
		return
	}
	if len(tc.monomorphicTransactions) == 0 {
		commitMonomorphicBindings(bindings)
		return
	}
	last := len(tc.monomorphicTransactions) - 1
	tc.monomorphicTransactions[last] = append(tc.monomorphicTransactions[last], bindings)
}

func (tc *TypeChecker) applyPendingMonomorphic(typ Type) Type {
	for _, transaction := range tc.monomorphicTransactions {
		for _, bindings := range transaction {
			typ = bindings.Apply(typ)
		}
	}
	return typ
}

func mergeMonomorphicBindings(pending []Substitution) (Substitution, bool) {
	combined := make(Substitution)
	unifier := NewUnifier()
	for _, bindings := range pending {
		for variable, typ := range bindings {
			left := combined.Apply(variable)
			right := combined.Apply(typ)
			next := unifier.Unify(left, right)
			if next == nil {
				return nil, false
			}
			combined = combined.Compose(next)
		}
	}
	return combined, true
}

func (tc *TypeChecker) finishMonomorphicTransaction(success bool) {
	last := len(tc.monomorphicTransactions) - 1
	pending := tc.monomorphicTransactions[last]
	tc.monomorphicTransactions = tc.monomorphicTransactions[:last]
	if !success {
		return
	}
	if len(tc.monomorphicTransactions) > 0 {
		parent := len(tc.monomorphicTransactions) - 1
		tc.monomorphicTransactions[parent] = append(tc.monomorphicTransactions[parent], pending...)
		return
	}
	merged, compatible := mergeMonomorphicBindings(pending)
	if !compatible {
		tc.addError(nil, "conflicting monomorphic specializations in one expression")
		return
	}
	commitMonomorphicBindings(merged)
}

func commitMonomorphicBindings(bindings Substitution) {
	committed := make(map[*monomorphicGroup]bool)
	for variable := range bindings {
		if variable == nil || variable.Monomorphic == nil || variable.monomorphicGroup == nil {
			continue
		}
		group := variable.monomorphicGroup
		if committed[group] {
			continue
		}
		local := make(Substitution)
		pending := make(map[*TypeVar]bool)
		for candidate := range bindings {
			if candidate != nil && candidate.monomorphicGroup == group {
				pending[candidate] = true
			}
		}
		for len(pending) > 0 {
			var current *TypeVar
			for candidate := range pending {
				current = candidate
				break
			}
			delete(pending, current)
			if _, included := local[current]; included {
				continue
			}
			value, ok := bindings[current]
			if !ok {
				continue
			}
			local[current] = value
			for _, dependency := range typeVarsIn(value) {
				// A fresh variable that escapes through a blocked solution becomes
				// part of the same persistent identity. Otherwise a later binding
				// keyed only by that variable would be discarded and reopen the
				// authority-bearing value polymorphically.
				if dependency.Monomorphic == nil {
					dependency.Monomorphic = variable.Monomorphic
					dependency.monomorphicGroup = group
				}
				if dependency.monomorphicGroup != group {
					continue
				}
				if _, bound := bindings[dependency]; bound {
					pending[dependency] = true
				}
			}
		}
		variable.Monomorphic.Commit(local)
		committed[group] = true
	}
}
