package compiler

import (
	"strings"
	"testing"
)

// reduce.tree is the balanced binary-counter tree — four elements group as
// simd.reduce_add does, five put the fifth on the right — and reduce.left
// is the sequential fold. A non-associative combine pins the grouping.
func TestE2EReduceTreeGrouping(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

r := import("reduce")

combine: (a: u32, b: u32): u32 = a * 31 + b
plus: (a: f32, b: f32): f32 = a + b

main: (): i32 = {
  xs: [5]u32 = [1, 2, 3, 4, 5]
  four: [4]u32 = [1, 2, 3, 4]
  empty: [0]u32 = []
  t5: u32 = r.tree(view(&xs), u32(0), combine)
  t4: u32 = r.tree(view(&four), u32(0), combine)
  t0: u32 = r.tree(view(&empty), u32(7), combine)
  l5: u32 = r.left(view(&xs), u32(0), combine)
  // Floats: the tree adds (a + b) + (c + d), which differs in bits from the
  // sequential sum for these values: 2^24 + 1 rounds back to 2^24, so the tree gives 2^24 + 2 and the left fold 2^24.
  fs: [4]f32 = [16777216.0, 1.0, 1.0, 1.0]
  zero: f32 = 0.0
  tf: f32 = r.tree(view(&fs), zero, plus)
  lf: f32 = r.left(view(&fs), zero, plus)
  ok1: Bool = t5 == ((1 * 31 + 2) * 31 + (3 * 31 + 4)) * 31 + 5
  ok2: Bool = t4 == (1 * 31 + 2) * 31 + (3 * 31 + 4)
  ok3: Bool = t0 == 7 && l5 == (((((0 * 31 + 1) * 31 + 2) * 31 + 3) * 31 + 4) * 31 + 5)
  ok4: Bool = tf == 16777218.0 && lf == 16777216.0
  i32(ok1 && ok2 && ok3 && ok4 ? 42 | 1)
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Operator laws: declared on an operator definition, validated against its
// signature, recorded for the tooling, printed back by the syntax.
func TestE2EOperatorLaws(t *testing.T) {
	src := `package main

Vec: type = struct { x: f32, y: f32 }
operator(+) add: (a: Vec, b: Vec): Vec laws { associative, commutative } = Vec { x: a.x + b.x, y: a.y + b.y }
operator(*) scale: (v: Vec, k: f32): Vec = Vec { x: v.x * k, y: v.y * k }

main: (): i32 = {
  v: Vec = Vec { x: 1.0, y: 2.0 } + Vec { x: 3.0, y: 4.0 } * 2.0
  i32(v.x == 7.0 && v.y == 10.0 ? 42 | 1)
}
`
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	model, err := New().WithPackageDir(root).SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	laws := model.TypeChecker.OperatorLaws()
	if len(laws) != 2 || laws[0].Function != "add" || laws[0].Law != "associative" || laws[1].Law != "commutative" || laws[0].Type != "Vec" || laws[0].Symbol != "+" {
		t.Fatalf("laws = %+v", laws)
	}
	if !model.TypeChecker.HasOperatorLaw("add", "associative") || model.TypeChecker.HasOperatorLaw("scale", "associative") {
		t.Fatal("HasOperatorLaw must answer for the declared function only")
	}
	tree, err := New().WithPackageDir(root).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	if printed := tree.Modules.Public.String(); !strings.Contains(printed, "laws { associative, commutative }") {
		t.Fatalf("laws must print back: %s", printed)
	}
	for name, bad := range map[string]string{
		"unknown":    "operator(+) add: (a: Vec, b: Vec): Vec laws { magic } = a",
		"twice":      "operator(+) add: (a: Vec, b: Vec): Vec laws { associative, associative } = a",
		"mismatch":   "operator(*) scale: (v: Vec, k: f32): Vec laws { commutative } = v",
		"nonoperand": "operator(==) same: (a: Vec, b: Vec): Bool laws { associative } = true",
		"plain":      "join: (a: Vec, b: Vec): Vec laws { associative } = a",
	} {
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": "package main\n\nVec: type = struct { x: f32, y: f32 }\n" + bad + "\n\nmain: (): i32 = 0\n"})
		if _, err := New().WithPackageDir(root).SemanticModel().Get(); err == nil {
			t.Fatalf("%s: laws clause must be rejected", name)
		}
	}
}

// A local binder that shares its name with a standard-library function
// (`left`, `tree`) is the local, whether or not the package is imported: the
// flat-name ownership check skips bound names (compiler/stdlib.go).
func TestE2EStdlibNamesShadowedByLocals(t *testing.T) {
	for name, src := range map[string]string{
		"unimported": `package main

main: (): i32 = {
  left: i32 = 40
  tree: i32 = 2
  left + tree
}
`,
		"imported": `package main

r := import("reduce")

add: (a: i32, b: i32): i32 = a + b

main: (): i32 = {
  xs: [2]i32 = [20, 21]
  left: i32 = r.left(view(&xs), i32(0), add)
  tree: i32 = 1
  left + tree
}
`,
	} {
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if abnormal || code != 42 {
			t.Fatalf("%s: exit=(%d,%v)", name, code, abnormal)
		}
	}
}
