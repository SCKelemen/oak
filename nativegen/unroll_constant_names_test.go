package nativegen

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func constantUnrollLoopNames(body ast.Expression) []string {
	var names []string
	walk(body, func(node ast.Node) {
		if loop, ok := node.(*ast.WhileStatement); ok {
			condition := loop.Condition.(*ast.InfixExpression)
			names = append(names, condition.Left.(*ast.Identifier).Value)
		}
	})
	return names
}

func TestUnrollConstantNamesSmallAndImmutable(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `f: (seed: u32): u32 {
	  total: u32 = seed
	  i: u32 = u32(0)
	  while i < u32(4) {
	    local: u32 = total + i
	    total = local + u32(1)
	    i = i + u32(1)
	  }
	  total + i
	}`, "f")
	before := cloneNode(fn.Body)
	first, changed := unrollConstantLoops(fn, fn.Body)
	second, changedAgain := unrollConstantLoops(fn, fn.Body)
	if !changed || !changedAgain || first == fn.Body || len(constantUnrollLoopNames(first)) != 0 {
		t.Fatalf("small recognized loop stayed rolled:\n%s", first.String())
	}
	if !reflect.DeepEqual(first, second) || !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("unrolling is nondeterministic or mutated its source")
	}
	if small, smallChanged := unrollSmallConstantLoops(fn, fn.Body); !smallChanged || !reflect.DeepEqual(small, first) {
		t.Fatal("small strategy changed the full strategy's fresh-name behavior")
	}
	declarations := map[string]int{}
	walk(first, func(node ast.Node) {
		if declaration, ok := node.(*ast.VariableDeclaration); ok {
			declarations[declaration.Name.Value]++
		}
	})
	for trip := range 4 {
		if declarations[tripName("local", int64(trip))] != 1 {
			t.Fatalf("trip %d lacks its unique local: %v", trip, declarations)
		}
	}
	if !strings.Contains(first.String(), "i = u32(4)") {
		t.Fatalf("final loop index was not retained:\n%s", first.String())
	}
	// Rewriting the result later must not mutate the original syntax.
	first.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration).Name.Value = "changed_output"
	if !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("output declaration aliases the source")
	}
}

func TestUnrollConstantNamesKeepOuterAfterInnerExpansion(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `f: (seed: u32): u32 {
	  total: u32 = seed
	  outer: u32 = u32(0)
	  while outer < u32(2) {
	    inner: u32 = u32(0)
	    while inner < u32(2) {
	      local: u32 = total + inner
	      total = local + outer
	      inner = inner + u32(1)
	    }
	    outer = outer + u32(1)
	  }
	  total
	}`, "f")
	// Retaining the outer loop prevents copying newly generated locals
	// using the outer matcher's declaration list from before inner expansion.
	before := cloneNode(fn.Body)
	got, changed := unrollConstantLoops(fn, fn.Body)
	if !changed || !reflect.DeepEqual(constantUnrollLoopNames(got), []string{"outer"}) {
		t.Fatalf("inner expansion duplicated the outer body:\n%s", got.String())
	}
	declarations := map[string]int{}
	walk(got, func(node ast.Node) {
		if declaration, ok := node.(*ast.VariableDeclaration); ok {
			declarations[declaration.Name.Value]++
		}
	})
	if declarations["local_t0"] != 1 || declarations["local_t1"] != 1 || declarations["local"] != 0 || declarations["inner"] != 1 {
		t.Fatalf("inner locals duplicated or lost: %v", declarations)
	}
	for name, count := range declarations {
		if count != 1 {
			t.Fatalf("duplicate generated declaration %s (%d)", name, count)
		}
	}
	if !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("nested rewriting mutated the source")
	}
	again, _ := unrollConstantLoops(fn, fn.Body)
	if !reflect.DeepEqual(got, again) {
		t.Fatal("nested expansion is nondeterministic")
	}
	if small, smallChanged := unrollSmallConstantLoops(fn, fn.Body); !smallChanged || !reflect.DeepEqual(small, got) {
		t.Fatal("small strategy lost the nested generated-name guard")
	}
}

func TestUnrollConstantNamesKeepLaterGeneratedCollision(t *testing.T) {
	fn, _, _, _ := checkedFillFunction(t, `f: (seed: u32): u32 {
	  total: u32 = seed
	  first: u32 = u32(0)
	  while first < u32(2) {
	    g: u32 = total + first
	    total = g + u32(1)
	    first = first + u32(1)
	  }
	  second: u32 = u32(0)
	  while second < u32(2) {
	    g: u32 = total + second
	    total = g + u32(1)
	    second = second + u32(1)
	  }
	  total
	}`, "f")
	before := cloneNode(fn.Body)
	got, changed := unrollConstantLoops(fn, fn.Body)
	if !changed || !reflect.DeepEqual(constantUnrollLoopNames(got), []string{"second"}) {
		t.Fatalf("later expansion reused previously generated local names:\n%s", got.String())
	}
	declarations := map[string]int{}
	walk(got, func(node ast.Node) {
		if declaration, ok := node.(*ast.VariableDeclaration); ok {
			declarations[declaration.Name.Value]++
		}
	})
	if declarations["g_t0"] != 1 || declarations["g_t1"] != 1 || declarations["g"] != 1 {
		t.Fatalf("generated or retained locals collided: %v", declarations)
	}
	if !reflect.DeepEqual(fn.Body, before) {
		t.Fatal("collision refusal mutated the source")
	}
	again, _ := unrollConstantLoops(fn, fn.Body)
	if !reflect.DeepEqual(got, again) {
		t.Fatal("generated-name reservation is nondeterministic")
	}
	if small, smallChanged := unrollSmallConstantLoops(fn, fn.Body); !smallChanged || !reflect.DeepEqual(small, got) {
		t.Fatal("small strategy lost the sequential generated-name guard")
	}
}
