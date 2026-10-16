package asm

import (
	"fmt"
	"math/rand"
	"reflect"
	"sync"
	"testing"
)

// Independent copy of the original componentBlaster leaf traversal. Keep its
// fresh seen map, edge order, and stopping rules as the differential oracle.
func referenceComponentAtomWalk(root *term, visit func(*term)) {
	seen := map[*term]bool{}
	var walk func(*term)
	walk = func(t *term) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		switch t.kind {
		case termParam:
			visit(t)
			return
		case termConst:
			return
		case termSelect:
			visit(t)
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

type componentAtomTestRead struct {
	span  string
	index *term
}

type componentAtomTestObservation struct {
	leaves  []*term
	writes  []string
	members map[string]bool
	reads   map[string]componentAtomTestRead
}

func observeComponentAtomWalk(walk func(*term, func(*term)), root *term) componentAtomTestObservation {
	out := componentAtomTestObservation{
		members: map[string]bool{},
		reads:   map[string]componentAtomTestRead{},
	}
	walk(root, func(t *term) {
		out.leaves = append(out.leaves, t)
		switch t.kind {
		case termParam:
			out.members[t.name] = true
			out.writes = append(out.writes, "member:"+t.name)
		case termSelect:
			key := fmt.Sprintf("read:%s:%p", t.name, t.left)
			out.reads[key] = componentAtomTestRead{t.name, t.left}
			out.writes = append(out.writes, "read:"+key)
			out.members[key] = true
			out.writes = append(out.writes, "member:"+key)
		}
	})
	return out
}

func checkComponentAtomAccounting(t *testing.T, m *componentAtoms) {
	t.Helper()
	if len(m.memo) > m.entryLimit {
		t.Fatalf("%d memo entries exceed cap %d", len(m.memo), m.entryLimit)
	}
	refs := 0
	for root, entry := range m.memo {
		if entry.building {
			t.Fatalf("unfinished entry for %p survived a query", root)
		}
		if len(entry.leaves) != cap(entry.leaves) {
			t.Fatalf("entry for %p has length %d but capacity %d", root, len(entry.leaves), cap(entry.leaves))
		}
		refs += len(entry.leaves)
	}
	if refs != m.leafRefs || refs > m.leafLimit {
		t.Fatalf("actual references %d, counted %d, cap %d", refs, m.leafRefs, m.leafLimit)
	}
}

func checkComponentAtomWalk(t *testing.T, m *componentAtoms, root *term) componentAtomTestObservation {
	t.Helper()
	want := observeComponentAtomWalk(referenceComponentAtomWalk, root)
	got := observeComponentAtomWalk(m.walk, root)
	// Compare pointers explicitly: reflect.DeepEqual on two *term values would
	// also accept pointer-distinct terms with recursively identical contents.
	if len(got.leaves) != len(want.leaves) {
		t.Fatalf("root %p: got %d leaves, want %d", root, len(got.leaves), len(want.leaves))
	}
	for i := range want.leaves {
		if got.leaves[i] != want.leaves[i] {
			t.Fatalf("root %p: leaf %d is %p, want %p", root, i, got.leaves[i], want.leaves[i])
		}
	}
	if !reflect.DeepEqual(got.writes, want.writes) || !reflect.DeepEqual(got.members, want.members) {
		t.Fatalf("root %p: membership/read insertion sequence differs: got %v, want %v", root, got.writes, want.writes)
	}
	if len(got.reads) != len(want.reads) {
		t.Fatalf("root %p: got %d reads, want %d", root, len(got.reads), len(want.reads))
	}
	for key, read := range want.reads {
		if actual, ok := got.reads[key]; !ok || actual != read {
			t.Fatalf("root %p: read %q is %#v, want %#v", root, key, actual, read)
		}
	}
	checkComponentAtomAccounting(t, m)
	return got
}

func TestComponentAtomsIdentityAndBoundaries(t *testing.T) {
	wide := &term{kind: termParam, name: "same", width: 64}
	narrow := &term{kind: termParam, name: "same", width: 8}
	indexA := &term{kind: termParam, name: "index", width: 32}
	indexB := &term{kind: termParam, name: "index", width: 32}
	readA := &term{kind: termSelect, name: "arena", left: indexA, width: 32}
	readB := &term{kind: termSelect, name: "arena", left: indexA, width: 32}
	readC := &term{kind: termSelect, name: "arena", left: indexB, width: 32}
	collision := &term{kind: termParam, name: fmt.Sprintf("read:arena:%p", indexA), width: 32}
	// Even populated fields beneath constants, params and selects are ignored.
	hidden := &term{kind: termParam, name: "hidden", width: 1}
	constant := &term{kind: termConst, cond: hidden, left: hidden, right: hidden, args: []*term{hidden}}
	wide.left = hidden
	readA.cond, readA.right, readA.args = hidden, hidden, []*term{hidden}
	shared := &term{kind: termApply, cond: wide, left: readA, right: narrow, args: []*term{readB, readC, wide, constant, nil}}
	root := &term{kind: termIte, width: 1, cond: narrow, left: shared, right: collision, args: []*term{readC, shared}}
	want := []*term{narrow, wide, readA, readB, readC, collision}
	m := newComponentAtoms()
	for repeat := 0; repeat < 3; repeat++ {
		got := checkComponentAtomWalk(t, m, root)
		if len(got.leaves) != len(want) {
			t.Fatalf("got %d leaves, want %d", len(got.leaves), len(want))
		}
		for i, leaf := range want {
			if got.leaves[i] != leaf {
				t.Fatalf("leaf %d is %p, want %p", i, got.leaves[i], leaf)
			}
		}
		if len(got.reads) != 2 || len(got.members) != 3 {
			t.Fatalf("got %d read keys and %d members, want 2 and 3", len(got.reads), len(got.members))
		}
		if _, ok := got.members["hidden"]; ok {
			t.Fatal("visited a field below a leaf boundary")
		}
		if _, ok := got.members["index"]; ok {
			t.Fatal("visited a select index while gathering its value's atoms")
		}
		checkComponentAtomWalk(t, m, shared)
		checkComponentAtomWalk(t, m, readA.left)
		checkComponentAtomWalk(t, m, readC.left)
		checkComponentAtomWalk(t, m, constant)
		checkComponentAtomWalk(t, m, nil)
	}
}

func TestComponentAtomsSharedDAGs(t *testing.T) {
	rng := rand.New(rand.NewSource(1937))
	for trial := 0; trial < 40; trial++ {
		nodes := []*term{nil, {kind: termConst}, {kind: termParam, name: "x", width: 8}, {kind: termParam, name: "x", width: 32}}
		for i := 0; i < 96; i++ {
			child := func() *term { return nodes[rng.Intn(len(nodes))] }
			var node *term
			switch rng.Intn(7) {
			case 0:
				node = &term{kind: termParam, name: fmt.Sprintf("p%d", rng.Intn(12)), width: 1 << rng.Intn(6)}
			case 1:
				node = &term{kind: termSelect, name: fmt.Sprintf("s%d", rng.Intn(4)), left: child(), width: 32}
			default:
				kinds := []termKind{termBinary, termCmp, termIte, termFloat, termApply, termQuant}
				node = &term{kind: kinds[rng.Intn(len(kinds))], op: "or", width: 1, cond: child(), left: child(), right: child()}
				for j := rng.Intn(5); j > 0; j-- {
					node.args = append(node.args, child())
				}
			}
			nodes = append(nodes, node)
		}
		for _, limits := range [][2]int{{componentAtomEntryLimit, componentAtomLeafLimit}, {9, 19}, {80, 3}, {0, 0}} {
			m := newComponentAtomsWithLimits(limits[0], limits[1])
			for pass := 0; pass < 2; pass++ {
				for i := len(nodes) - 1; i >= 0; i-- {
					checkComponentAtomWalk(t, m, nodes[i])
				}
			}
		}
	}
}

func TestComponentAtomsDeepAndNestedBoolean(t *testing.T) {
	x := &term{kind: termParam, name: "x", width: 1}
	y := &term{kind: termParam, name: "y", width: 1}
	root := &term{kind: termCmp, left: x, right: y, width: 1}
	nodes := []*term{root}
	for i := 0; i < 4096; i++ {
		if i%2 == 0 {
			root = &term{kind: termBinary, op: "or", left: root, right: root, width: 1}
		} else {
			root = &term{kind: termIte, cond: x, left: root, right: y, width: 1}
		}
		nodes = append(nodes, root)
	}
	m := newComponentAtoms()
	checkComponentAtomWalk(t, m, root)
	entries, refs := len(m.memo), m.leafRefs
	for i := len(nodes) - 1; i >= 0; i -= 257 {
		checkComponentAtomWalk(t, m, nodes[i])
	}
	if m.fallback || len(m.memo) != entries || m.leafRefs != refs {
		t.Fatal("repeated subgraph queries did not reuse their completed entries")
	}
	checkComponentAtomWalk(t, newComponentAtomsWithLimits(32, 64), root)
}

func TestComponentAtomsCapsAndPartialBuilds(t *testing.T) {
	x := &term{kind: termParam, name: "x", width: 1}
	y := &term{kind: termParam, name: "y", width: 1}
	root := &term{kind: termBinary, op: "or", left: x, right: y, width: 1}
	for _, test := range []struct {
		name             string
		entries, leaves  int
		wantEntries      int
		wantRefs         int
		wantRoot, capped bool
	}{
		{"exact", 3, 4, 3, 4, true, false},
		{"union cap", 3, 3, 2, 2, false, true},
		{"leaf cap", 3, 1, 1, 1, false, true},
		{"entry cap", 2, 4, 1, 1, false, true},
		{"zero leaves", 3, 0, 0, 0, false, true},
		{"zero entries", 0, 4, 0, 0, false, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			m := newComponentAtomsWithLimits(test.entries, test.leaves)
			checkComponentAtomWalk(t, m, root)
			_, hasRoot := m.memo[root]
			if len(m.memo) != test.wantEntries || m.leafRefs != test.wantRefs || hasRoot != test.wantRoot || m.fallback != test.capped {
				t.Fatalf("entries=%d refs=%d root=%v fallback=%v", len(m.memo), m.leafRefs, hasRoot, m.fallback)
			}
			// Successful child entries survive a failed parent. Both later
			// child queries and full fallback queries must replay exactly once.
			for _, query := range []*term{x, y, root, root, x} {
				checkComponentAtomWalk(t, m, query)
			}
			if test.capped && (len(m.memo) != test.wantEntries || m.leafRefs != test.wantRefs) {
				t.Fatal("uncached queries grew the memo after reaching a cap")
			}
		})
	}
}

func TestComponentAtomsEmptyEntriesCount(t *testing.T) {
	constant := &term{kind: termConst}
	empty := &term{kind: termApply, left: constant, args: []*term{nil, constant}}
	for _, entries := range []int{1, 2} {
		m := newComponentAtomsWithLimits(entries, 0)
		checkComponentAtomWalk(t, m, nil)
		if len(m.memo) != 0 {
			t.Fatal("nil consumed a memo entry")
		}
		checkComponentAtomWalk(t, m, constant)
		if len(m.memo) != 1 || m.leafRefs != 0 {
			t.Fatal("constant must consume one entry and no leaf references")
		}
		checkComponentAtomWalk(t, m, empty)
		if len(m.memo) != entries || m.leafRefs != 0 || m.fallback != (entries == 1) {
			t.Fatalf("entries=%d refs=%d fallback=%v", len(m.memo), m.leafRefs, m.fallback)
		}
	}
}

func TestComponentAtomsCycleFallback(t *testing.T) {
	x := &term{kind: termParam, name: "x", width: 1}
	y := &term{kind: termParam, name: "y", width: 1}
	a := &term{kind: termIte, cond: x, width: 1}
	b := &term{kind: termApply, left: a, args: []*term{y}}
	a.left, a.right = b, y
	m := newComponentAtoms()
	for _, root := range []*term{a, b, x, a, y, b} {
		checkComponentAtomWalk(t, m, root)
	}
	if !m.fallback {
		t.Fatal("cycle did not select the original walker")
	}
	if _, ok := m.memo[a]; ok {
		t.Fatal("cyclic root retained a context-dependent entry")
	}
	if _, ok := m.memo[b]; ok {
		t.Fatal("cyclic child retained a context-dependent entry")
	}
	self := &term{kind: termBinary, right: x, width: 1}
	self.left = self
	checkComponentAtomWalk(t, newComponentAtoms(), self)
	// Cycles hidden behind a select are outside this traversal's boundary.
	read := &term{kind: termSelect, name: "arena", left: self, width: 8}
	leafOnly := newComponentAtoms()
	checkComponentAtomWalk(t, leafOnly, read)
	if leafOnly.fallback || len(leafOnly.memo) != 1 {
		t.Fatal("select-index cycle leaked across the leaf boundary")
	}
}

func TestComponentAtomsInvocationIsolation(t *testing.T) {
	x := &term{kind: termParam, name: "x", width: 8}
	y := &term{kind: termParam, name: "y", width: 8}
	index := &term{kind: termParam, name: "index", width: 32}
	read := &term{kind: termSelect, name: "before", left: index, width: 8}
	root := &term{kind: termApply, left: x, args: []*term{read}}
	first := newComponentAtoms()
	checkComponentAtomWalk(t, first, root)
	// A new componentBlaster invocation builds a fresh cache even if another
	// verifier phase has changed the same term pointers between invocations.
	root.left, root.args = y, []*term{x, read}
	x.name, x.width = "renamed", 32
	read.name, read.left = "after", y
	second := newComponentAtoms()
	got := checkComponentAtomWalk(t, second, root)
	if len(got.leaves) != 3 || got.leaves[0] != y || got.leaves[1] != x || got.leaves[2] != read {
		t.Fatal("new invocation reused stale atom structure")
	}
	if _, ok := got.members["renamed"]; !ok {
		t.Fatal("new invocation reused stale member names")
	}
	// A replay belongs to its supplied destination maps; it must not depend
	// on the reads or members collected by an earlier callback.
	checkComponentAtomWalk(t, second, root)
}

func TestComponentAtomsConcurrentCollectors(t *testing.T) {
	x := &term{kind: termParam, name: "x", width: 1}
	y := &term{kind: termParam, name: "y", width: 1}
	root := &term{kind: termCmp, left: x, right: y, width: 1}
	nodes := []*term{x, y, root}
	for i := 0; i < 128; i++ {
		root = &term{kind: termIte, cond: x, left: root, right: y, args: []*term{root}, width: 1}
		nodes = append(nodes, root)
	}
	snapshots := make([]term, len(nodes))
	wants := make([]componentAtomTestObservation, len(nodes))
	for i, node := range nodes {
		snapshots[i] = *node
		snapshots[i].args = append([]*term(nil), node.args...)
		wants[i] = observeComponentAtomWalk(referenceComponentAtomWalk, node)
	}
	var workers sync.WaitGroup
	collectors := make(chan *componentAtoms, 8)
	for i := 0; i < 8; i++ {
		workers.Add(1)
		go func() {
			defer workers.Done()
			m := newComponentAtoms()
			defer func() { collectors <- m }()
			for i := len(nodes) - 1; i >= 0; i-- {
				got, want := observeComponentAtomWalk(m.walk, nodes[i]), wants[i]
				if len(got.leaves) != len(want.leaves) {
					t.Errorf("node %d: got %d leaves, want %d", i, len(got.leaves), len(want.leaves))
					return
				}
				for j, leaf := range want.leaves {
					if got.leaves[j] != leaf {
						t.Errorf("node %d: leaf %d is %p, want %p", i, j, got.leaves[j], leaf)
						return
					}
				}
				if !reflect.DeepEqual(got.writes, want.writes) || !reflect.DeepEqual(got.members, want.members) {
					t.Errorf("node %d: callback writes differ", i)
					return
				}
			}
		}()
	}
	workers.Wait()
	close(collectors)
	for m := range collectors {
		checkComponentAtomAccounting(t, m)
	}
	for i, node := range nodes {
		before := snapshots[i]
		if node.kind != before.kind || node.width != before.width || node.declared != before.declared || node.id != before.id || node.name != before.name || node.value != before.value || node.op != before.op || node.sigBits != before.sigBits || node.cond != before.cond || node.left != before.left || node.right != before.right || len(node.args) != len(before.args) {
			t.Fatalf("collector mutated shared term %d", i)
		}
		for j, arg := range before.args {
			if node.args[j] != arg {
				t.Fatalf("collector mutated shared term %d argument %d", i, j)
			}
		}
	}
}
