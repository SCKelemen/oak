package compiler

import (
	"strings"
	"testing"
)

// Declaring the order once (docs/spec/55-parallelism.md section 4; the ml
// pilot's F3 and RFC 0004): `order tree|left|bounded { }` names the order
// of every reduce.reduce inside it. The exact tree is the default, `left`
// is the sequential fold, and `bounded` regroups only a combine declaring
// associative — an operator or a plain binary function — refused otherwise.
const orderScopeProgram = `package main

r := import("reduce")

Sum: type = struct { v: u32 }

operator(+) add: (a: Sum, b: Sum): Sum laws { associative } = Sum { v: a.v + b.v }
combine: (a: u32, b: u32): u32 = a * 31 + b
plus: (a: f32, b: f32): f32 = a + b
fadd: (a: f32, b: f32): f32 laws { associative, commutative, identity(0.0) } = a + b

main: (): i32 = {
  xs: [5]u32 = [1, 2, 3, 4, 5]
  fs: [4]f32 = [16777216.0, 1.0, 1.0, 1.0]
  sums: [3]Sum = [Sum { v: 1 }, Sum { v: 2 }, Sum { v: 3 }]
  zero: f32 = 0.0
  bare: u32 = r.reduce(view(&xs), u32(0), combine)
  treed: u32 = 0
  folded: u32 = 0
  tf: f32 = 0.0
  lf: f32 = 0.0
  bf: f32 = 0.0
  exact: f32 = 0.0
  total: u32 = 0
  order tree {
    treed = r.reduce(view(&xs), u32(0), combine)
    tf = r.reduce(view(&fs), zero, plus)
  }
  order left {
    folded = r.reduce(view(&xs), u32(0), combine)
    lf = r.reduce(view(&fs), zero, plus)
    order tree {
      treed = treed + r.reduce(view(&xs), u32(0), combine)
    }
  }
  order bounded {
    total = r.reduce(view(&sums), Sum { v: 0 }, add).v
    bf = r.reduce(view(&fs), zero, fadd)
    exact = r.tree(view(&fs), zero, fadd)
  }
  tree5: u32 = ((1 * 31 + 2) * 31 + (3 * 31 + 4)) * 31 + 5
  left5: u32 = ((((0 * 31 + 1) * 31 + 2) * 31 + 3) * 31 + 4) * 31 + 5
  bare == tree5 && treed == tree5 + tree5 && folded == left5 && tf == 16777218.0 && lf == 16777216.0 && total == 6 && bf == 16777216.0 && exact == 16777218.0 ? 42 | 1
}
`

func TestE2EOrderScopes(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": orderScopeProgram})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	// Each call is rewritten to the order its scope named.
	for _, want := range []string{"oak_reduce__tree_u32(", "oak_reduce__left_u32(", "oak_reduce__left_f32(", "oak_reduce__tree_f32(", "oak_reduce__chain_Sum(", "oak_reduce__chain_f32("} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
	if strings.Contains(emitted, "reduce__reduce_") {
		t.Fatalf("every reduce.reduce must resolve to a named order:\n%s", emitted)
	}
	model, err := New().WithPackageDir(root).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	if n := len(model.TypeChecker.LawLowerings()); n != 8 {
		t.Fatalf("the semantic model lists every resolved call, got %d", n)
	}
	// The declaration prints back as written.
	tree, err := New().WithPackageDir(root).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	if printed := tree.Root.String(); !strings.Contains(printed, "order left {") || !strings.Contains(printed, "order bounded {") {
		t.Fatalf("order blocks must print back:\n%s", printed)
	}
}

// `bounded` is the permission to regroup, and it is refused without the
// claim; `any` is not an order.
func TestE2EOrderBoundedNeedsTheClaim(t *testing.T) {
	src := `package main

r := import("reduce")

plus: (a: f32, b: f32): f32 = a + b

main: (): i32 = {
  fs: [4]f32 = [1.0, 2.0, 3.0, 4.0]
  zero: f32 = 0.0
  s: f32 = 0.0
  order bounded {
    s = r.reduce(view(&fs), zero, plus)
  }
  s == 10.0 ? 42 | 1
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "regroups only a combine declaring laws { associative }") {
		t.Fatalf("order bounded without the claim must be refused: %v", err)
	}
	bad := strings.Replace(src, "order bounded {", "order sideways {", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": bad})
	if _, err := New().WithPackageDir(root).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "the order is tree, left, or bounded") {
		t.Fatalf("an unknown order is a parse error: %v", err)
	}
	// There is no unchecked order: `any` names none, and the message says
	// what to write instead.
	unchecked := strings.Replace(src, "order bounded {", "order any {", 1)
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": unchecked})
	if _, err := New().WithPackageDir(root).EmitC().Get(); err == nil || !strings.Contains(err.Error(), "no unchecked order") || !strings.Contains(err.Error(), "order bounded") {
		t.Fatalf("order any must be refused by name: %v", err)
	}
	// `order` stays an ordinary identifier elsewhere.
	plain := "package main\n\nmain: (): i32 = {\n  order: u32 = 42\n  order == u32(42) ? 42 | 1\n}\n"
	root = writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": plain})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("order as a binding: exit=(%d,%v)", code, abnormal)
	}
}
