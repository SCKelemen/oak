package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParsesIndexedADTConstructorResults(t *testing.T) {
	input := `Expr[T]: type =
		| Int: i64 => Expr[i64]
		| Flag: Bool => Expr[Bool]`
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parser errors: %v", errors)
	}
	if len(program.Statements) != 1 {
		t.Fatalf("statements = %d, want 1", len(program.Statements))
	}
	decl, ok := program.Statements[0].(*ast.ADTType)
	if !ok {
		t.Fatalf("statement = %T, want *ast.ADTType", program.Statements[0])
	}
	if len(decl.TypeParams) != 1 || decl.TypeParams[0].Name.Value != "T" {
		t.Fatalf("type parameters = %#v", decl.TypeParams)
	}
	if len(decl.Variants) != 2 {
		t.Fatalf("variants = %d, want 2", len(decl.Variants))
	}
	for _, variant := range decl.Variants {
		if variant.Result == nil {
			t.Fatalf("variant %s has no result type", variant.Name.Value)
		}
	}
}

func TestParsesIndexedResultsInPrefixTypeForm(t *testing.T) {
	input := `type Expr[T]: type = | Int: i64 => Expr[i64] | Flag: Bool => Expr[Bool]`
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parser errors: %v", errors)
	}
	if len(program.Statements) != 1 {
		t.Fatalf("statements = %d, want 1", len(program.Statements))
	}
	decl, ok := program.Statements[0].(*ast.ADTType)
	if !ok || len(decl.Variants) != 2 {
		t.Fatalf("prefix-form declaration = %#v", program.Statements[0])
	}
}
