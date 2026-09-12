package compiler

import (
	"strings"
	"testing"
)

// A backend consuming a declared law (docs/spec/10-syntax.md section 14a;
// the ml pilot's F3): reduce.tree over an operator declaring
// laws { associative } is lowered to reduce.chain — the left fold from the
// first element, no stack of partials — by Oak.Reduce.tree_eq_chainFold.
// Without the law the tree named is the tree computed.
const lawfulTreeProgram = `package main

r := import("reduce")

Sum: type = struct { v: u32 }

operator(+) add: (a: Sum, b: Sum): Sum laws { associative } = Sum { v: a.v + b.v }

main: (): i32 = {
  xs: [5]Sum = [Sum { v: 1 }, Sum { v: 2 }, Sum { v: 3 }, Sum { v: 4 }, Sum { v: 5 }]
  empty: [0]Sum = []
  t: Sum = r.tree(view(&xs), Sum { v: 0 }, add)
  e: Sum = r.tree(view(&empty), Sum { v: 7 }, add)
  t.v == 15 && e.v == 7 ? 42 | 1
}
`

func TestE2ELawLowersTreeToChain(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": lawfulTreeProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "oak_reduce__chain_Sum(") || strings.Contains(emitted, "reduce__tree_Sum") {
		t.Fatalf("a tree over an associative operator lowers to chain:\n%s", emitted)
	}
	model, err := New().WithPackageDir(root).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	lowerings := model.TypeChecker.LawLowerings()
	if len(lowerings) != 2 || lowerings[0].Function != "add" || lowerings[0].From != "reduce__tree" || lowerings[0].To != "reduce__chain" {
		t.Fatalf("lowerings = %+v", lowerings)
	}

	// Without the law, the grouping named is the grouping computed.
	unlawful := strings.Replace(lawfulTreeProgram, " laws { associative }", "", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": unlawful})
	emitted, err = New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(emitted, "oak_reduce__tree_Sum(") || strings.Contains(emitted, "reduce__chain_Sum") {
		t.Fatalf("without the law the tree stays:\n%s", emitted)
	}
}

// A false law is the author's: declaring floating-point addition
// associative makes the regrouped result the chain's, which differs from
// the tree named — 2^24 + 1 rounds back to 2^24 in the chain, while the
// tree adds (2^24 + 1) + (1 + 1) = 2^24 + 2.
func TestE2EFalseLawRegroups(t *testing.T) {
	program := `package main

r := import("reduce")

F: type = struct { x: f32 }

operator(+) fadd: (a: F, b: F): F laws { associative } = F { x: a.x + b.x }
plus: (a: F, b: F): F = F { x: a.x + b.x }

main: (): i32 = {
  fs: [4]F = [F { x: 16777216.0 }, F { x: 1.0 }, F { x: 1.0 }, F { x: 1.0 }]
  zero: F = F { x: 0.0 }
  regrouped: F = r.tree(view(&fs), zero, fadd)
  named: F = r.tree(view(&fs), zero, plus)
  regrouped.x == 16777216.0 && named.x == 16777218.0 ? 42 | 1
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": program})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
