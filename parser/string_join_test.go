package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// Two string literals joined by `+` are one literal (docs/spec/10-syntax.md
// section 2a): the parser folds them, pairwise from the left.
func TestStringLiteralsJoin(t *testing.T) {
	p := New(scanner.New("x: string = \"float \" + \"acc\" + \"[0]\"\n"))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	decl, ok := program.Statements[0].(*ast.VariableDeclaration)
	if !ok {
		t.Fatalf("statement = %T", program.Statements[0])
	}
	lit, ok := decl.Value.(*ast.StringLiteral)
	if !ok || lit.Value != "float acc[0]" {
		t.Fatalf("value = %s (%T)", decl.Value.String(), decl.Value)
	}
	// A literal beside a value stays an infix expression for the checker.
	p = New(scanner.New("y: u32 = \"a\" + n\n"))
	program = p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatal(p.Errors())
	}
	if _, ok := program.Statements[0].(*ast.VariableDeclaration).Value.(*ast.InfixExpression); !ok {
		t.Fatalf("a literal beside a value must not fold: %s", program.Statements[0].String())
	}
}
