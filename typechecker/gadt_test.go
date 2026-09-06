package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

func indexedType(name, index string) ast.Expression {
	return &ast.IndexExpression{
		Left:  &ast.Identifier{Value: name},
		Index: &ast.Identifier{Value: index},
	}
}

func indexedExprDecl() *ast.ADTType {
	return &ast.ADTType{
		Name: &ast.Identifier{Value: "Expr"},
		TypeParams: []*ast.TypeParameter{{
			Name: &ast.Identifier{Value: "T"},
		}},
		Variants: []*ast.ADTVariant{
			{Name: &ast.Identifier{Value: "Int"}, Payload: &ast.Identifier{Value: "i64"}, Result: indexedType("Expr", "i64")},
			{Name: &ast.Identifier{Value: "Flag"}, Payload: &ast.Identifier{Value: "Bool"}, Result: indexedType("Expr", "Bool")},
			{Name: &ast.Identifier{Value: "Id"}, Payload: &ast.Identifier{Value: "T"}, Result: indexedType("Expr", "T")},
		},
	}
}

func TestGADTResultIndicesRestrictReachableCases(t *testing.T) {
	tc := New(object.NewEnvironment())
	tc.checkADTType(indexedExprDecl())
	if errors := tc.Errors(); len(errors) != 0 {
		t.Fatalf("declaration errors: %v", errors)
	}

	scrutinee := &GenericType{Name: "Expr", TypeArgs: []Type{&PrimitiveType{Name: "i64"}}}
	expr := &ast.MatchExpression{
		Scrutinee: &ast.Identifier{Value: "x"},
		Arms: []*ast.MatchArm{
			{Pattern: variantPattern("Int", &ast.BindingPattern{Name: &ast.Identifier{Value: "n"}}), Body: &ast.IntegerLiteral{Value: 1}},
			{Pattern: variantPattern("Flag", &ast.BindingPattern{Name: &ast.Identifier{Value: "b"}}), Body: &ast.StringLiteral{Value: "impossible"}},
			{Pattern: variantPattern("Id", &ast.BindingPattern{Name: &ast.Identifier{Value: "v"}}), Body: &ast.IntegerLiteral{Value: 0}},
		},
	}
	tc.env.SetType("x", scrutinee)
	analysis := tc.analyzeMatch(expr, scrutinee)
	if len(analysis.Missing) != 0 {
		t.Fatalf("missing = %#v", analysis.Missing)
	}
	if analysis.Arms[1].Reachable || !analysis.Arms[1].Impossible {
		t.Fatalf("Flag arm should be index-impossible: %#v", analysis.Arms[1])
	}
	if got := analysis.Arms[2].Refinements[0].Equalities; len(got) != 1 || got[0].Parameter != "T" || got[0].Type != "i64" {
		t.Fatalf("Id equalities = %#v", got)
	}
}

func TestGADTConstructorRejectsWrongExpectedIndex(t *testing.T) {
	tc := New(object.NewEnvironment())
	tc.checkADTType(indexedExprDecl())
	expr := &ast.VariantExpression{
		TypeName: &ast.Identifier{Value: "Expr"},
		Variant:  &ast.Identifier{Value: "Flag"},
		Payload:  &ast.Boolean{Value: true},
	}
	expected := &GenericType{Name: "Expr", TypeArgs: []Type{&PrimitiveType{Name: "i64"}}}
	if got := tc.checkVariantExpression(expr, expected); got != nil {
		t.Fatalf("constructor type = %v, want nil", got)
	}
	for _, diagnostic := range tc.Diagnostics() {
		if diagnostic.Code == CodeGADTResultMismatch {
			return
		}
	}
	t.Fatalf("expected %s, got %#v", CodeGADTResultMismatch, tc.Diagnostics())
}

func TestParsesGenericADTTypeApplication(t *testing.T) {
	tc := New(object.NewEnvironment())
	got := tc.parseTypeExpression(indexedType("Expr", "i64"))
	want := &GenericType{Name: "Expr", TypeArgs: []Type{&PrimitiveType{Name: "i64"}}}
	if got == nil || !got.Equals(want) {
		t.Fatalf("type = %v, want %v", got, want)
	}
}
