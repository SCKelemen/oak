package lowering

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func aggregateTestIndex(name string) *ast.IndexExpression {
	return &ast.IndexExpression{
		Left:  &ast.Identifier{Value: name},
		Index: &ast.Identifier{Value: "i"},
	}
}

func aggregateTestCoreIndex(t *testing.T, expression ast.Expression) {
	t.Helper()
	call, ok := expression.(*ast.InvocationExpression)
	if !ok {
		t.Fatalf("lowered expression = %T, want invocation", expression)
	}
	callee, ok := call.Function.(*ast.Identifier)
	if !ok || callee.Value != "core_index" || len(call.Arguments) != 2 {
		t.Fatalf("lowered invocation = %#v, want core_index with two arguments", call)
	}
}

func TestLowerExpressionCopiesArrayLiteralAndLowersElements(t *testing.T) {
	typeSyntax := &ast.Identifier{Value: "u32"}
	index := aggregateTestIndex("values")
	original := &ast.ArrayLiteral{
		Type:     typeSyntax,
		Elements: []ast.Expression{index, &ast.IntegerLiteral{Value: 7}},
	}

	lowered, ok := lowerExpression(original, nil).(*ast.ArrayLiteral)
	if !ok {
		t.Fatalf("lowered expression = %T, want array literal", lowered)
	}
	if lowered == original || &lowered.Elements[0] == &original.Elements[0] {
		t.Fatal("array literal or its element slice was reused")
	}
	if lowered.Type != typeSyntax {
		t.Fatal("typed array prefix was expression-lowered or copied")
	}
	aggregateTestCoreIndex(t, lowered.Elements[0])
	if original.Elements[0] != index {
		t.Fatal("checked array literal was mutated")
	}
}

func TestLowerExpressionCopiesRecordLiteralCoherently(t *testing.T) {
	index := aggregateTestIndex("values")
	nested := &ast.ArrayLiteral{Elements: []ast.Expression{index}}
	manifest := &ast.Identifier{Value: "Shared"}
	record := &ast.RecordLiteral{
		Fields: map[string]ast.Expression{"items": nested},
		FieldOrder: []ast.RecordField{{
			Name: "items", Value: nested, Manifest: manifest, Align: 32,
			Tags: []ast.FieldTag{{Name: "json", Value: &ast.StringLiteral{Value: "items"}}},
		}},
		Extension: &ast.Identifier{Value: "row"},
		TypeName:  &ast.Identifier{Value: "Box"},
		Layout:    &ast.RecordLayoutSpec{Align: 64},
	}

	lowered, ok := lowerExpression(record, nil).(*ast.RecordLiteral)
	if !ok {
		t.Fatalf("lowered expression = %T, want record literal", lowered)
	}
	if lowered == record || len(lowered.FieldOrder) != 1 || len(lowered.Fields) != 1 {
		t.Fatalf("record copy shape = %#v", lowered)
	}
	if lowered.Extension != record.Extension || lowered.TypeName != record.TypeName || lowered.Layout != record.Layout {
		t.Fatal("record type/layout metadata was changed")
	}
	field := lowered.FieldOrder[0]
	if field.Manifest != manifest || field.Align != 32 || len(field.Tags) != 1 {
		t.Fatal("record field metadata was changed")
	}
	if lowered.Fields["items"] != field.Value {
		t.Fatal("Fields and FieldOrder do not share the same lowered value")
	}
	array, ok := field.Value.(*ast.ArrayLiteral)
	if !ok || len(array.Elements) != 1 {
		t.Fatalf("lowered nested field = %#v", field.Value)
	}
	aggregateTestCoreIndex(t, array.Elements[0])
	if record.FieldOrder[0].Value != nested || record.Fields["items"] != nested {
		t.Fatal("checked record literal was mutated")
	}
}

func TestLowerExpressionKeepsLegacyRecordMapOnly(t *testing.T) {
	record := &ast.RecordLiteral{
		Fields: map[string]ast.Expression{"item": aggregateTestIndex("values")},
	}
	lowered := lowerExpression(record, nil).(*ast.RecordLiteral)
	if len(lowered.FieldOrder) != 0 || len(lowered.Fields) != 1 {
		t.Fatalf("map-only record acquired an order: %#v", lowered)
	}
	aggregateTestCoreIndex(t, lowered.Fields["item"])
}
