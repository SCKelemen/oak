package compiler

import (
	"reflect"
	"sync"
	"testing"

	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

// The uncached traversal is an independent compatibility oracle for the field
// plan. In particular, unexported fields and arrays retain their old behavior.
func walkSyntaxUncached(v reflect.Value, visit func(any) bool) {
	switch v.Kind() {
	case reflect.Interface, reflect.Pointer:
		if v.IsNil() {
			return
		}
		if v.Kind() == reflect.Pointer && !visit(v.Interface()) {
			return
		}
		walkSyntaxUncached(v.Elem(), visit)
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Type().Field(i).IsExported() {
				walkSyntaxUncached(v.Field(i), visit)
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			walkSyntaxUncached(v.Index(i), visit)
		}
	case reflect.Map:
		it := v.MapRange()
		for it.Next() {
			walkSyntaxUncached(it.Value(), visit)
		}
	}
}

type syntaxWalkFixture struct {
	ID     int
	Child  *syntaxWalkFixture
	Any    any
	List   []*syntaxWalkFixture
	hidden *syntaxWalkFixture
	Array  [1]*syntaxWalkFixture
}

func TestWalkSyntaxOrderPruningAndMutation(t *testing.T) {
	leaf := &syntaxWalkFixture{ID: 3}
	child := &syntaxWalkFixture{ID: 2, Child: leaf}
	root := &syntaxWalkFixture{ID: 1, Child: child, Any: leaf, List: []*syntaxWalkFixture{leaf, nil}, hidden: &syntaxWalkFixture{ID: 99}, Array: [1]*syntaxWalkFixture{{ID: 100}}}
	trace := func(walk func(reflect.Value, func(any) bool), prune int) []int {
		var out []int
		walk(reflect.ValueOf(root), func(v any) bool { n := v.(*syntaxWalkFixture); out = append(out, n.ID); return n.ID != prune })
		return out
	}
	for _, prune := range []int{-1, 1, 2, 3} {
		got, want := trace(walkSyntax, prune), trace(walkSyntaxUncached, prune)
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("prune %d: got %v want %v", prune, got, want)
		}
	}
	if got := trace(walkSyntax, -1); !reflect.DeepEqual(got, []int{1, 2, 3, 3, 3}) {
		t.Fatal("order, shared occurrence, or visibility changed", got)
	}
	// Warming the plan must not snapshot values. Replacements remain visible.
	root.Child = &syntaxWalkFixture{ID: 4}
	if got := trace(walkSyntax, -1); !reflect.DeepEqual(got, []int{1, 4, 3, 3}) {
		t.Fatal("stale AST values", got)
	}
	// Visitors may mutate a node before descent, as compiler rewrites do.
	walkSyntax(reflect.ValueOf(root), func(v any) bool {
		if v == root {
			root.Child = leaf
		}
		return true
	})
	if got := trace(walkSyntax, -1); !reflect.DeepEqual(got, []int{1, 3, 3, 3}) {
		t.Fatal("visitor mutation lost", got)
	}
}

func TestWalkSyntaxRealTrees(t *testing.T) {
	for _, name := range []string{"time", "json"} {
		t.Run(name, func(t *testing.T) {
			p := parser.New(layout.New(scanner.New(stdlib.Packages[name])))
			tree := p.ParseProgram()
			if errs := p.Errors(); len(errs) != 0 {
				t.Fatal(errs)
			}
			count := func(walk func(reflect.Value, func(any) bool)) map[any]int {
				out := map[any]int{}
				walk(reflect.ValueOf(tree), func(node any) bool { out[node]++; return true })
				return out
			}
			// Map fields intentionally keep Go's unspecified order; compare pointer
			// occurrence counts over the actual parsed trees, not map iteration order.
			if got, want := count(walkSyntax), count(walkSyntaxUncached); !reflect.DeepEqual(got, want) {
				t.Fatal("pointer visits differ from uncached traversal")
			}
		})
	}
}

func TestWalkSyntaxConcurrentPlans(t *testing.T) {
	// This type is not used by the other tests, so concurrent first-use plan
	// publication is exercised too. Each visitor owns its mutable state.
	type cold struct {
		Value  *int
		Hidden struct{ secret *int }
	}
	value := 7
	root := &cold{Value: &value}
	var wg sync.WaitGroup
	for i := 0; i < 16; i++ {
		wg.Go(func() {
			for j := 0; j < 50; j++ {
				visits := 0
				walkSyntax(reflect.ValueOf(root), func(any) bool { visits++; return true })
				if visits != 2 {
					t.Errorf("got %d visits, want 2", visits)
					return
				}
			}
		})
	}
	wg.Wait()
}
