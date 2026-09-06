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

func TestCompilationTypeModelSeparatesRecordAndStructRepresentation(t *testing.T) {
	const source = `
Shape: type = { x: u8, y: u32 }
Stored: type = struct { x: u8, y: u32 }
`

	module, err := New().WithSource("records.oak", source).TypeModel().Get()
	if err != nil {
		t.Fatalf("type model projection failed: %v", err)
	}
	if len(module.Definitions) != 2 {
		t.Fatalf("expected two semantic definitions, got %d", len(module.Definitions))
	}

	shape := module.Definitions[0]
	stored := module.Definitions[1]
	if shape.Type.Kind != semir.TypeRecord || stored.Type.Kind != semir.TypeRecord {
		t.Fatalf("expected both declarations to have record semantics: shape=%#v stored=%#v", shape.Type, stored.Type)
	}
	if shape.Representation.Kind != semir.RepresentationUnspecified || shape.Representation.Policy != semir.RepresentationPolicyUnspecified || shape.Representation.Resolved {
		t.Fatalf("plain record unexpectedly selected representation: %#v", shape.Representation)
	}
	if stored.Representation.Kind != semir.RepresentationRecord {
		t.Fatalf("struct did not select record representation: %#v", stored.Representation)
	}
	if stored.Representation.Policy != semir.RepresentationPolicyNaturalOrdered {
		t.Fatalf("struct selected wrong policy: %#v", stored.Representation)
	}
	if stored.Representation.Resolved {
		t.Fatalf("struct representation should remain unresolved before target field representations are known: %#v", stored.Representation)
	}
	if stored.Representation.Alignment != 0 || stored.Representation.Size != 0 || len(stored.Representation.Fields) != 0 {
		t.Fatalf("struct projection invented numeric layout facts: %#v", stored.Representation)
	}
}

func TestBuildTypeModelPreservesRecordOrderWithoutInventingLayout(t *testing.T) {
	record := &ast.RecordLiteral{Fields: make(map[string]ast.Expression)}
	record.AddField(ast.Identifier{}.Token, "y", &ast.Identifier{Value: "i32"})
	record.AddField(ast.Identifier{}.Token, "x", &ast.Identifier{Value: "i32"})
	program := &ast.Program{Statements: []ast.Statement{
		&ast.ADTType{
			Name: &ast.Identifier{Value: "Point"},
			Variants: []*ast.ADTVariant{
				{Name: &ast.Identifier{Value: "Point"}, Literal: record},
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
	if point.Representation.Kind != semir.RepresentationUnspecified || point.Representation.Policy != semir.RepresentationPolicyUnspecified || point.Representation.Resolved || len(point.Representation.Fields) != 0 {
		t.Fatalf("projector invented ABI representation: %#v", point.Representation)
	}
	if got := []string{point.Type.Fields[0].Name, point.Type.Fields[1].Name}; got[0] != "y" || got[1] != "x" {
		t.Fatalf("expected source field order [y x], got %v", got)
	}
}

func TestBuildTypeModelRejectsRecordWithoutSourceOrder(t *testing.T) {
	program := &ast.Program{Statements: []ast.Statement{
		&ast.ADTType{
			Name: &ast.Identifier{Value: "Legacy"},
			Variants: []*ast.ADTVariant{{
				Name: &ast.Identifier{Value: "Legacy"},
				Literal: &ast.RecordLiteral{Fields: map[string]ast.Expression{
					"x": &ast.Identifier{Value: "i32"},
				}},
			}},
		},
	}}
	_, err := BuildTypeModel(program)
	if err == nil || !strings.Contains(err.Error(), "source order is unavailable") {
		t.Fatalf("expected fail-closed record-order error, got %v", err)
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


func TestCompilationTypeModelPreservesIndexedConstructorResults(t *testing.T) {
	const source = `Expr[T]: type =
  | Int: i64 => Expr[i64]
  | Id: T => Expr[T]`

	module, err := New().WithSource("expr.oak", source).TypeModel().Get()
	if err != nil {
		t.Fatalf("type model projection failed: %v", err)
	}
	if len(module.Definitions) != 1 || len(module.Definitions[0].Type.Variants) != 2 {
		t.Fatalf("unexpected indexed ADT model: %#v", module)
	}
	variants := module.Definitions[0].Type.Variants
	if variants[0].Result != "Expr[i64]" || variants[1].Result != "Expr[T]" {
		t.Fatalf("constructor results were not preserved: %#v", variants)
	}
}
