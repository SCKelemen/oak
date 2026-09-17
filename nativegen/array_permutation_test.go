package nativegen

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func permutationLiteral(name string, indices ...int64) *ast.ArrayLiteral {
	elements := make([]ast.Expression, len(indices))
	for i, index := range indices {
		elements[i] = &ast.IndexExpression{Left: &ast.Identifier{Value: name}, Index: &ast.IntegerLiteral{Value: index}}
	}
	return &ast.ArrayLiteral{Elements: elements}
}

func TestSelfPermutationRecognition(t *testing.T) {
	g := &generator{layouts: map[string]*recordLayout{}}
	arr := &arrayLocal{elem: scalars["u32"], length: 4}
	valid := permutationLiteral("state", 1, 0, 3, 2)
	block := &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{&ast.ExpressionStatement{Expression: valid}}}}

	for _, test := range []struct {
		name  string
		value ast.Expression
		ok    bool
	}{
		{name: "direct", value: valid, ok: true},
		{name: "inlined helper block", value: block, ok: true},
		{name: "duplicate index", value: permutationLiteral("state", 1, 0, 2, 2)},
		{name: "wrong source", value: permutationLiteral("other", 1, 0, 3, 2)},
		{name: "out of range", value: permutationLiteral("state", 1, 0, 3, 4)},
		{name: "preceding statement", value: &ast.BlockExpression{Block: &ast.BlockStatement{Statements: []ast.Statement{
			&ast.ExpressionStatement{Expression: &ast.IntegerLiteral{Value: 0}},
			&ast.ExpressionStatement{Expression: valid},
		}}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			_, ok := g.selfPermutation("state", arr, test.value)
			if ok != test.ok {
				t.Fatalf("recognized = %v, want %v", ok, test.ok)
			}
		})
	}
}
