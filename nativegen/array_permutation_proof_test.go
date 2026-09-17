package nativegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// objects counts the frame arrays the lowering leaves: an array whose
// every use is a constant-index element, a permutation of itself, or the
// body's result is scalar-replaced (nativegen/scalar_arrays.go) and
// leaves none; the proof is over the same values either way.
func verifyArrayPermutation(t *testing.T, source string, objects int) {
	t.Helper()
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	functions := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok {
			functions[fn.Name.Value] = fn
			symbols[fn.Name.Value] = true
		}
	}
	fn := functions["shuffle"]
	if fn == nil {
		t.Fatal("missing shuffle function")
	}
	body, err := CompileFor(Lane{Arch: asm.ArchArm64}, fn, functions, nil, nil, nil, nil)
	if err != nil {
		t.Fatal(err)
	}
	body.Callees = functions
	if findings := asm.Check(body, fn, symbols); len(findings) != 0 {
		t.Fatalf("checker: %v\n%s", findings, Describe(body))
	}
	if v := asm.Verify(body, fn, fn.Body); v.Kind != asm.VerdictProven {
		t.Fatalf("want proven, got %s: %s\n%s", v.Kind, v.Message, Describe(body))
	}
	if got := len(FrameObjects(body)); got != objects {
		t.Fatalf("frame arrays = %d, want %d\n%s", got, objects, Describe(body))
	}
}

// Verify the emitted cycle moves against Oak's snapshot assignment for
// every permutation of five arbitrary words, including fixed points,
// disjoint cycles, and cycles in both directions. No concrete input can
// hide a lost or overwritten source element in these proofs.
func TestArrayPermutationAllFiveWordOrders(t *testing.T) {
	order := []int{0, 1, 2, 3, 4}
	var visit func(int)
	visit = func(at int) {
		if at == len(order) {
			var elements []string
			for _, k := range order {
				elements = append(elements, fmt.Sprintf("a[%d]", k))
			}
			source := "shuffle: (input: [5]u32): [5]u32 {\n  a: [5]u32 = input\n  a = [5]u32{ " + strings.Join(elements, ", ") + " }\n  a\n}\n"
			t.Run(fmt.Sprint(order), func(t *testing.T) { verifyArrayPermutation(t, source, 0) })
			return
		}
		for k := at; k < len(order); k++ {
			order[at], order[k] = order[k], order[at]
			visit(at + 1)
			order[at], order[k] = order[k], order[at]
		}
	}
	visit(0)
}

func TestArrayPermutationIntegerWidths(t *testing.T) {
	for _, typ := range []string{"u32", "i32", "u64", "i64"} {
		t.Run(typ, func(t *testing.T) {
			source := fmt.Sprintf("shuffle: (input: [5]%[1]s): [5]%[1]s {\n  a: [5]%[1]s = input\n  a = [5]%[1]s{ a[4], a[3], a[1], a[2], a[0] }\n  a\n}\n", typ)
			verifyArrayPermutation(t, source, 0)
		})
	}
}

func TestArrayPermutationLongCycles(t *testing.T) {
	for _, n := range []int{64, 65} {
		t.Run(fmt.Sprint(n), func(t *testing.T) {
			var elements []string
			for i := 0; i < n; i++ {
				elements = append(elements, fmt.Sprintf("a[%d]", (i+1)%n))
			}
			source := fmt.Sprintf("shuffle: (input: [%d]u64): [%d]u64 {\n  a: [%d]u64 = input\n  a = [%d]u64{ %s }\n  a\n}\n", n, n, n, n, strings.Join(elements, ", "))
			verifyArrayPermutation(t, source, 1)
		})
	}
}

func TestArrayPermutationRepeatedReadsKeepSnapshot(t *testing.T) {
	// A gather is not a permutation. Keep the temporary: writing a[0]
	// before evaluating the second read would lose input[0].
	verifyArrayPermutation(t, "shuffle: (input: [5]u32): [5]u32 {\n  a: [5]u32 = input\n  a = [5]u32{ a[1], a[0], a[0], a[3], a[4] }\n  a\n}\n", 0)
}

func TestArrayPermutationOtherArrayUsesNormalAssignment(t *testing.T) {
	verifyArrayPermutation(t, "shuffle: (input: [5]u32): [5]u32 {\n  a: [5]u32 = input\n  a = [5]u32{ input[4], input[3], input[2], input[1], input[0] }\n  a\n}\n", 0)
}

func TestArrayPermutationPreservesHelperStatements(t *testing.T) {
	verifyArrayPermutation(t, "reverse: (input: [5]u32): [5]u32 {\n  b: [5]u32 = input\n  b[0] = u32(99)\n  [5]u32{ b[4], b[3], b[2], b[1], b[0] }\n}\n\nshuffle: (input: [5]u32): [5]u32 {\n  a: [5]u32 = input\n  a = reverse(a)\n  a\n}\n", 2)
}

func TestArrayPermutationExpandedHelper(t *testing.T) {
	verifyArrayPermutation(t, "reverse: (a: [5]u32): [5]u32 = [5]u32{ a[4], a[3], a[2], a[1], a[0] }\n\nshuffle: (input: [5]u32): [5]u32 {\n  a: [5]u32 = input\n  a = reverse(a)\n  a\n}\n", 0)
}

func TestArrayPermutationRefusesUnprovenShapes(t *testing.T) {
	literal := func(indices ...int64) *ast.ArrayLiteral {
		out := &ast.ArrayLiteral{}
		for _, k := range indices {
			out.Elements = append(out.Elements, &ast.IndexExpression{Left: &ast.Identifier{Value: "a"}, Index: &ast.IntegerLiteral{Value: k}})
		}
		return out
	}
	valid := func() *ast.ArrayLiteral { return literal(4, 3, 2, 1, 0) }
	withIndex := func(index ast.Expression) *ast.ArrayLiteral {
		out := valid()
		out.Elements[0].(*ast.IndexExpression).Index = index
		return out
	}
	for name, expr := range map[string]ast.Expression{
		"duplicate": literal(4, 3, 2, 1, 1),
		"negative":  literal(-1, 3, 2, 1, 0),
		"past end":  literal(5, 3, 2, 1, 0),
		"short":     literal(3, 2, 1, 0),
		"dynamic":   withIndex(&ast.Identifier{Value: "i"}),
		"call":      withIndex(&ast.InvocationExpression{Function: &ast.Identifier{Value: "next_index"}}),
		"discarded block": &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: valid(), Discard: true},
		}}},
		"effect before literal": &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.InvocationExpression{Function: &ast.Identifier{Value: "touch"}}},
			&ast.ExpressionStatement{Expression: valid()},
		}}},
	} {
		t.Run(name, func(t *testing.T) {
			g := &generator{}
			arr := &arrayLocal{elem: scalars["u32"], length: 5}
			if source, recognized := g.selfPermutation("a", arr, expr); recognized || source != nil {
				t.Fatalf("unsupported assignment recognized: %v", source)
			}
		})
	}
	for _, arr := range []*arrayLocal{
		{elem: scalars["u32"], length: 5, readOnly: true},
		{elem: scalars["u32"], length: 5, inReg: true},
		{elem: scalars["u32"], length: 5, paramRef: true},
		{elem: scalars["Bool"], length: 5},
		nil,
	} {
		g := &generator{}
		if source, recognized := g.selfPermutation("a", arr, valid()); recognized || source != nil {
			t.Fatalf("unsupported array recognized: %+v", arr)
		}
	}
}
