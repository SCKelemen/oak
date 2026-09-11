package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"testing"
)

func parseElmExpression(t *testing.T, input string) ast.Expression {
	t.Helper()
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parse errors: %v", errs)
	}
	return program.Statements[0].(*ast.ExpressionStatement).Expression
}

func TestPipelineAppendsValueAsFinalArgument(t *testing.T) {
	expr := parseElmExpression(t, "value |> f(1)")
	call, ok := expr.(*ast.InvocationExpression)
	if !ok {
		t.Fatalf("got %T", expr)
	}
	if call.Function.String() != "f" || len(call.Arguments) != 2 || call.Arguments[1].String() != "value" {
		t.Fatalf("pipeline lowered to %s, want f(1, value)", call.String())
	}
}

func TestPipelineFieldAccessor(t *testing.T) {
	expr := parseElmExpression(t, "person |> .name")
	field, ok := expr.(*ast.IndexExpression)
	if !ok || !field.Dot || field.String() != "(person.name)" {
		t.Fatalf("got %T %s", expr, expr.String())
	}
}

func TestLowercaseDotIsAccessorUppercaseDotIsVariant(t *testing.T) {
	if _, ok := parseElmExpression(t, ".name").(*ast.FieldAccessorExpression); !ok {
		t.Fatal(".name must be an accessor")
	}
	if _, ok := parseElmExpression(t, ".Ok").(*ast.VariantExpression); !ok {
		t.Fatal(".Ok must remain a variant")
	}
}

func TestParsesExtensibleRecordTypeSyntax(t *testing.T) {
	expr := parseElmExpression(t, "{ r | name: string, age: u8 }")
	record := expr.(*ast.RecordLiteral)
	if record.Extension == nil || record.Extension.Value != "r" || len(record.Fields) != 2 {
		t.Fatalf("unexpected row: %#v", record)
	}
}
