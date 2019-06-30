package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestTypeDeclarationStatements(t *testing.T) {
	input := `
	type ReaderWriterCloser 
		= Reader
		& Writer
		& Closer;

	type ReaderWriter
		= Reader
		& Writer;
	`

	lxr := scanner.New(input)
	p := New(lxr)

	program := p.ParseProgram()
	if program == nil {
		t.Fatalf("ParseProgram() return nil, which isn't ideal.")
	}
	if len(program.Statements) != 2 {
		t.Fatalf("program doesn't have the correct number of statements. Expected 2, received %d", len(program.Statements))
	}

	tests := []struct {
		expectedIdentifier string
	}{
		{"ReaderWriterCloser"},
		{"ReaderWriter"},
	}

	for i, tt := range tests {
		stmt := program.Statements[i]
		if stmt.TokenLiteral() != "type" {
			t.Errorf("s.TokenLiteral not 'type', received %q", stmt.TokenLiteral())
			return
		}

		typeDeclaration, ok := stmt.(*ast.TypeDeclarationStatement)
		if !ok {
			t.Errorf("statement not of type *ast.TypeDeclarationStatement, received %T", stmt)
			return
		}

		if typeDeclaration.Name.Value != tt.expectedIdentifier {
			t.Errorf("statement.Name.Value not '%s', received %s", tt.expectedIdentifier, typeDeclaration.Name.Value)
			return
		}

		if typeDeclaration.Name.TokenLiteral() != tt.expectedIdentifier {
			t.Errorf("statement.Name.TokenLiteral() not '%s', received %s", tt.expectedIdentifier, typeDeclaration.Name.TokenLiteral())
			return
		}

	}
}
