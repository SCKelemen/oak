package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestTypeDeclarationDistinguishesRecordAndStruct(t *testing.T) {
	input := `
Shape: type = { x: u8, y: u32 }
Stored: type = struct { x: u8, y: u32 }
`

	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("parser errors: %v", errors)
	}
	if len(program.Statements) != 2 {
		t.Fatalf("expected two declarations, got %d", len(program.Statements))
	}

	assertProductToken := func(index int, want token.TokenKind) {
		t.Helper()
		declaration, ok := program.Statements[index].(*ast.ADTType)
		if !ok {
			t.Fatalf("statement %d is %T, want *ast.ADTType", index, program.Statements[index])
		}
		if len(declaration.Variants) != 1 {
			t.Fatalf("declaration %q has %d variants, want 1", declaration.Name.Value, len(declaration.Variants))
		}
		record, ok := declaration.Variants[0].Literal.(*ast.RecordLiteral)
		if !ok {
			t.Fatalf("declaration %q literal is %T, want *ast.RecordLiteral", declaration.Name.Value, declaration.Variants[0].Literal)
		}
		if record.Token.TokenKind != want {
			t.Fatalf("declaration %q product token=%s, want %s", declaration.Name.Value, record.Token.TokenKind, want)
		}
		if got := record.OrderedFields(); len(got) != 2 || got[0].Name != "x" || got[1].Name != "y" {
			t.Fatalf("declaration %q lost field order: %#v", declaration.Name.Value, got)
		}
	}

	assertProductToken(0, token.LBRACE)
	assertProductToken(1, token.STRUCT)
}
