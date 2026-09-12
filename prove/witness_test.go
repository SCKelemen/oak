package prove

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
)

// The witness rewrite installs a driver over the enumerable parameters and
// leaves the rest to the interpreter; the driver's exit status maps back
// to the theorem that failed.
func TestWitnessRewrite(t *testing.T) {
	src := `
Color: type = Red | Green | Blue
next: (c: Color): Color = c ? | .Red => .Green | .Green => .Blue | .Blue => .Red
cycle: theorem (c: Color) { next(next(next(c))) == c }
add_commutes: theorem (x: u8, y: u8) { x + y == y + x }
wide: theorem (x: u32) { x + u32(0) == x }
main: (): i32 = 0
`
	results := []Result{
		{Name: "cycle", Status: Decided, Detail: "all 3 cases"},
		{Name: "add_commutes", Status: Decided, Detail: "all 65536 cases"},
		{Name: "wide", Status: Decided, Detail: "at the bit level (9 BDD nodes)"},
	}
	var plan WitnessPlan
	model, err := compiler.New().WithSyntaxRewrite(WitnessRewrite(results, &plan)).WithSource("w.oak", src).Check().Get()
	if err != nil {
		t.Fatalf("the driver must check: %v", err)
	}
	if strings.Join(plan.Covered, ",") != "cycle,add_commutes" || len(plan.Skipped) != 0 {
		t.Fatalf("plan: %+v", plan)
	}
	text := ""
	for _, stmt := range model.Tree.Root.Statements {
		if fn, isFn := stmt.(*ast.FunctionStatement); isFn && fn.Name != nil && fn.Name.Value == "main" {
			text = fn.String()
		}
	}
	for _, want := range []string{"witness_k0 < u32(3)", ".Red", ".Blue", "u8_trunc_u32(witness_k1)", "add_commutes(x, y)"} {
		if !strings.Contains(text, want) {
			t.Fatalf("driver lacks %q:\n%s", want, text)
		}
	}
	applied := ApplyWitness(append([]Result(nil), results...), plan, 2)
	if applied[1].Status != Refuted || !strings.Contains(applied[1].Detail, "disagrees") || !strings.Contains(applied[0].Detail, "witnessed") || strings.Contains(applied[2].Detail, "witnessed") {
		t.Fatalf("applied: %+v", applied)
	}
	// A theorem over a record is left to the interpreter.
	results = []Result{{Name: "rec", Status: Decided, Detail: "all 4 cases"}}
	plan = WitnessPlan{}
	if _, err := compiler.New().WithSyntaxRewrite(WitnessRewrite(results, &plan)).WithSource("r.oak", "P: type = struct { a: Bool, b: Bool }\nrec: theorem (p: P) { p.a || !p.a }\nmain: (): i32 = 0\n").Check().Get(); err != nil {
		t.Fatal(err)
	}
	if len(plan.Covered) != 0 || !strings.Contains(plan.Skipped["rec"], "not enumerable") {
		t.Fatalf("plan: %+v", plan)
	}
}
