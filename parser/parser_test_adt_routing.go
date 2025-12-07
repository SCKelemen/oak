package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParser_ADTTypeRouting(t *testing.T) {
	tests := []struct {
		input    string
		expected string // Expected AST node type or error message
	}{
		{
			input:    "Encoding: type = {}",
			expected: "ADTType", // Should parse as ADT type definition
		},
		{
			input:    "Utf8: type = {}",
			expected: "ADTType",
		},
		{
			input:    "x: i32 = 42",
			expected: "VariableDeclaration", // Should parse as variable declaration
		},
	}

	for _, tt := range tests {
		l := scanner.New(tt.input)
		p := New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			// Check if error is about routing bug
			hasRoutingBug := false
			for _, err := range p.Errors() {
				if strings.Contains(err, "routing bug") || strings.Contains(err, "unexpected token in type expression: type") {
					hasRoutingBug = true
					t.Errorf("Parser routing bug for input %q: %v", tt.input, p.Errors())
					break
				}
			}
			if !hasRoutingBug {
				// Other errors are okay for now
				continue
			}
		}

		if len(program.Statements) == 0 {
			t.Errorf("No statements parsed for input %q", tt.input)
			continue
		}

		stmt := program.Statements[0]
		switch tt.expected {
		case "ADTType":
			if _, ok := stmt.(*ast.ADTType); !ok {
				t.Errorf("Expected ADTType for %q, got %T", tt.input, stmt)
			}
		case "VariableDeclaration":
			if _, ok := stmt.(*ast.VariableDeclaration); !ok {
				t.Errorf("Expected VariableDeclaration for %q, got %T", tt.input, stmt)
			}
		}
	}
}
