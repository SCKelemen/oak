package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

func TestCompilationTypeModelProjectsADT(t *testing.T) {
	const source = `Color: type = Red | Green | Blue`

	module, err := New().WithSource("color.oak", source).TypeModel().Get()
	if err != nil {
		t.Fatalf("type model projection failed: %v", err)
	}
	if len(module.Definitions) != 1 {
		t.Fatalf("expected one semantic definition, got %d", len(module.Definitions))
	}
	color := module.Definitions[0]
	if color.Name != "Color" || color.Type.Kind != semir.TypeSum {
		t.Fatalf("unexpected Color definition: %#v", color)
	}
	if len(color.Type.Variants) != 3 {
		t.Fatalf("expected three variants, got %d", len(color.Type.Variants))
	}
}

func TestBuildTypeModelProjectsRecordWithoutInventingLayout(t *testing.T) {
	program := &ast.Program{Statements: []ast.Statement{
		&ast.ADTType{
			Name: &ast.Identifier{Value: "Point"},
			Variants: []*ast.ADTVariant{
				{
					Name: &ast.Identifier{Value: "Point"},
					Literal: &ast.RecordLiteral{Fields: map[string]ast.Expression{
						"y": &ast.Identifier{Value: "i32"},
						"x": &ast.Identifier{Value: "i32"},
					}},
				},
			},
		},
	}}

	module, err := BuildTypeModel(program)
	if err != nil {
		t.Fatalf("record projection failed: %v", err)
	}
	point := module.Definitions[0]
	if point.Type.Kind != semir.TypeRecord {
		t.Fatalf("expected record semantic type, got %q", point.Type.Kind)
	}
	if point.Representation.Kind != semir.RepresentationUnspecified || len(point.Representation.Fields) != 0 {
		t.Fatalf("projector invented representation from unordered AST: %#v", point.Representation)
	}
	if got := []string{point.Type.Fields[0].Name, point.Type.Fields[1].Name}; got[0] != "x" || got[1] != "y" {
		t.Fatalf("expected deterministic semantic field order [x y], got %v", got)
	}
}

func TestBuildTypeModelProjectsInterfaceMethods(t *testing.T) {
	program := &ast.Program{Statements: []ast.Statement{
		&ast.InterfaceType{
			Name: &ast.Identifier{Value: "Readable"},
			Methods: []*ast.InterfaceMethod{
				{
					Name:       &ast.Identifier{Value: "Read"},
					ReturnType: &ast.Identifier{Value: "ReadResult"},
					Parameters: []*ast.FunctionParameter{
						{Name: &ast.Identifier{Value: "buf"}, Type: &ast.IndexExpression{Left: &ast.Identifier{Value: "u8"}, Index: &ast.Identifier{Value: ""}}},
					},
				},
			},
		},
	}}

	module, err := BuildTypeModel(program)
	if err != nil {
		t.Fatalf("interface projection failed: %v", err)
	}
	readable := module.Definitions[0]
	if readable.Type.Kind != semir.TypeInterface || len(readable.Type.Methods) != 1 {
		t.Fatalf("unexpected interface projection: %#v", readable.Type)
	}
	method := readable.Type.Methods[0]
	if method.Name != "Read" || method.Parameters[0].Type != "[]u8" || method.Return != "ReadResult" {
		t.Fatalf("unexpected method projection: %#v", method)
	}
}

func TestBuildTypeModelRejectsAmbiguousLegacyVariantLiteral(t *testing.T) {
	program := &ast.Program{Statements: []ast.Statement{
		&ast.ADTType{
			Name: &ast.Identifier{Value: "Status"},
			Variants: []*ast.ADTVariant{
				{
					Name:    &ast.Identifier{Value: "Ok"},
					Payload: &ast.Identifier{Value: "u16"},
					Literal: &ast.IntegerLiteral{Value: 200},
				},
			},
		},
	}}

	_, err := BuildTypeModel(program)
	if err == nil || !strings.Contains(err.Error(), "legacy literal syntax") {
		t.Fatalf("expected ambiguous-literal error, got %v", err)
	}
}

func TestSemanticTypeNameFlattensGenericArguments(t *testing.T) {
	expr := &ast.IndexExpression{
		Left: &ast.IndexExpression{
			Left:  &ast.Identifier{Value: "Result"},
			Index: &ast.Identifier{Value: "T"},
		},
		Index: &ast.Identifier{Value: "E"},
	}

	got, err := semanticTypeName(expr)
	if err != nil {
		t.Fatalf("generic type projection failed: %v", err)
	}
	if got != "Result[T, E]" {
		t.Fatalf("expected Result[T, E], got %q", got)
	}
}
