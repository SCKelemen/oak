package compiler

import (
	"strings"
	"testing"
)

// The consumer of a declared law (docs/spec/10-syntax.md section 14a; the
// ml pilot's F3 and RFC 0004): inside `order bounded { }` a reduce.reduce
// over a combine declaring laws { associative } is lowered to reduce.chain
// — the left fold from the first element, no stack of partials — by
// Oak.Reduce.tree_eq_chainFold. An explicit reduce.tree keeps its name,
// law or no law: the grouping named is the grouping computed.
const lawfulTreeProgram = `package main

r := import("reduce")

Sum: type = struct { v: u32 }

operator(+) add: (a: Sum, b: Sum): Sum laws { associative } = Sum { v: a.v + b.v }

main: (): i32 = {
  xs: [5]Sum = [Sum { v: 1 }, Sum { v: 2 }, Sum { v: 3 }, Sum { v: 4 }, Sum { v: 5 }]
  empty: [0]Sum = []
  t: Sum = r.tree(view(&xs), Sum { v: 0 }, add)
  e: Sum = r.tree(view(&empty), Sum { v: 7 }, add)
  b: Sum = Sum { v: 0 }
  order bounded {
    b = r.reduce(view(&xs), Sum { v: 0 }, add)
  }
  t.v == 15 && e.v == 7 && b.v == 15 ? 42 | 1
}
`

func TestE2ETreeKeepsItsNameBoundedRegroups(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": lawfulTreeProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "oak_reduce__tree_Sum(") || !strings.Contains(emitted, "oak_reduce__chain_Sum(") {
		t.Fatalf("an explicit tree stays a tree; the bounded reduce lowers to chain:\n%s", emitted)
	}
	model, err := New().WithPackageDir(root).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	lowerings := model.TypeChecker.LawLowerings()
	if len(lowerings) != 1 || lowerings[0].Function != "add" || lowerings[0].From != "reduce__reduce" || lowerings[0].To != "reduce__chain" {
		t.Fatalf("lowerings = %+v", lowerings)
	}

	// Without the law, the bounded block is refused, and the trees stand.
	unlawful := strings.Replace(lawfulTreeProgram, " laws { associative }", "", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": unlawful})
	if _, err := New().WithPackageDir(root).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "regroups only a combine declaring laws { associative }") {
		t.Fatalf("bounded without the law must be refused: %v", err)
	}
}

// A false law is the author's: declaring floating-point addition
// associative makes the bounded result the chain's, which differs from the
// tree named — 2^24 + 1 rounds back to 2^24 in the chain, while the tree
// adds (2^24 + 1) + (1 + 1) = 2^24 + 2. The claim sits on the plain f32
// function itself, as the ml pilot's `add with associative` does.
func TestE2EFalseLawRegroups(t *testing.T) {
	program := `package main

r := import("reduce")

fadd: (a: f32, b: f32): f32 laws { associative } = a + b
plus: (a: f32, b: f32): f32 = a + b

main: (): i32 = {
  fs: [4]f32 = [16777216.0, 1.0, 1.0, 1.0]
  zero: f32 = 0.0
  regrouped: f32 = 0.0
  order bounded {
    regrouped = r.reduce(view(&fs), zero, fadd)
  }
  named: f32 = r.tree(view(&fs), zero, fadd)
  plain: f32 = r.tree(view(&fs), zero, plus)
  regrouped == 16777216.0 && named == 16777218.0 && plain == 16777218.0 ? 42 | 1
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": program})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
