package asm

const (
	componentAtomEntryLimit = 1 << 16
	componentAtomLeafLimit  = 1 << 20
)

// componentAtoms belongs to one componentBlaster invocation. Terms must remain
// unchanged during that invocation; no cache is stored on the terms themselves.
// A result contains distinct leaf pointers in their first DFS discovery order,
// not distinct names or read keys: replay must preserve every original callback.
type componentAtoms struct {
	memo       map[*term]componentAtomEntry
	entryLimit int
	leafLimit  int
	leafRefs   int
	fallback   bool
}

type componentAtomEntry struct {
	leaves   []*term
	building bool
}

func newComponentAtoms() *componentAtoms {
	return newComponentAtomsWithLimits(componentAtomEntryLimit, componentAtomLeafLimit)
}

func newComponentAtomsWithLimits(entries, leaves int) *componentAtoms {
	return &componentAtoms{
		memo:       make(map[*term]componentAtomEntry),
		entryLimit: entries,
		leafLimit:  leaves,
	}
}

// walk gathers parameters and reads, stopping before a read's index. A caller
// can walk that index separately, just as componentBlaster did before caching.
// The callback may update the caller's maps, but must not mutate the terms.
func (m *componentAtoms) walk(root *term, visit func(*term)) {
	if leaves, ok := m.collect(root); ok {
		for _, leaf := range leaves {
			visit(leaf)
		}
		return
	}
	// A cap or a cycle uses precisely the original fresh-seen traversal. In
	// particular, a cycle must not leave a context-dependent partial result.
	seen := map[*term]bool{}
	var walk func(*term)
	walk = func(t *term) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		switch t.kind {
		case termParam, termSelect:
			visit(t)
			return
		case termConst:
			return
		}
		walk(t.cond)
		walk(t.left)
		walk(t.right)
		for _, arg := range t.args {
			walk(arg)
		}
	}
	walk(root)
}

func (m *componentAtoms) collect(t *term) ([]*term, bool) {
	if t == nil {
		return nil, true
	}
	if entry, ok := m.memo[t]; ok {
		if entry.building {
			// Terms are normally DAGs, but the old walker also tolerated
			// cycles. Only completely built acyclic entries remain reusable.
			m.fallback = true
			return nil, false
		}
		return entry.leaves, true
	}
	if m.fallback {
		return nil, false
	}
	if len(m.memo) >= m.entryLimit {
		m.fallback = true
		return nil, false
	}
	// Empty and in-progress entries count toward the entry cap as well.
	m.memo[t] = componentAtomEntry{building: true}
	leaves, ok := m.build(t)
	if !ok {
		delete(m.memo, t)
		return nil, false
	}
	m.memo[t] = componentAtomEntry{leaves: leaves}
	m.leafRefs += len(leaves)
	return leaves, true
}

func (m *componentAtoms) build(t *term) ([]*term, bool) {
	switch t.kind {
	case termParam, termSelect:
		if m.leafRefs >= m.leafLimit {
			m.fallback = true
			return nil, false
		}
		return []*term{t}, true
	case termConst:
		return nil, true
	}
	// Finish every child before constructing this node's union. There are
	// consequently no partially accumulated union lists on the recursion stack.
	for i := 0; i < 3+len(t.args); i++ {
		if _, ok := m.collect(componentAtomChild(t, i)); !ok {
			return nil, false
		}
	}
	remaining := m.leafLimit - m.leafRefs
	seen := map[*term]bool{}
	for i := 0; i < 3+len(t.args); i++ {
		for _, leaf := range m.memo[componentAtomChild(t, i)].leaves {
			if !seen[leaf] {
				if len(seen) >= remaining {
					m.fallback = true
					return nil, false
				}
				seen[leaf] = true
			}
		}
	}
	// leafRefs counts sum(len(entry.leaves)). Each slice has exact capacity,
	// including zero for an empty result, so the retained backing slots obey
	// the same cap. The one temporary union set has at most remaining keys;
	// together with retained/final slices it uses at most twice the leaf cap
	// in live leaf references, plus map capacity/metadata and the separately
	// capped memo keys. This is a retention bound, not an exact byte bound.
	leaves := make([]*term, 0, len(seen))
	clear(seen)
	for i := 0; i < 3+len(t.args); i++ {
		for _, leaf := range m.memo[componentAtomChild(t, i)].leaves {
			if !seen[leaf] {
				seen[leaf] = true
				leaves = append(leaves, leaf)
			}
		}
	}
	return leaves, true
}

func componentAtomChild(t *term, i int) *term {
	switch i {
	case 0:
		return t.cond
	case 1:
		return t.left
	case 2:
		return t.right
	default:
		return t.args[i-3]
	}
}
