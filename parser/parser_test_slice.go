package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParser_SliceExpression(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected string
	}{
		{
			"two-index slice",
			"arr[1:5]",
			"(arr[1:5])",
		},
		{
			"slice with start only",
			"arr[1:]",
			"(arr[1:])",
		},
		{
			"slice with end only",
			"arr[:5]",
			"(arr[:5])",
		},
		{
			"full slice",
			"arr[:]",
			"(arr[:])",
		},
		{
			"slice with negative index",
			"arr[-1:5]",
			"(arr[(-1):5])",
		},
		{
			"slice with both negative",
			"arr[-5:-1]",
			"(arr[(-5):(-1)])",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			l := New(scanner.New(tt.input))
			program := l.ParseProgram()

			if len(l.Errors()) > 0 {
				t.Fatalf("Parser errors: %v", l.Errors())
			}

			if len(program.Statements) != 1 {
				t.Fatalf("Expected 1 statement, got %d", len(program.Statements))
			}

			stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
			if !ok {
				t.Fatalf("Expected ExpressionStatement, got %T", program.Statements[0])
			}

			actual := stmt.Expression.String()
			if actual != tt.expected {
				t.Errorf("Expected %q, got %q", tt.expected, actual)
			}
		})
	}
}

func TestParser_SliceExpression_Chained(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected string
	}{
		{
			"chained slices",
			"arr[1:5][2:4]",
			"((arr[1:5])[2:4])",
		},
		{
			"slice after index",
			"arr[0][1:3]",
			"((arr[0])[1:3])",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			l := New(scanner.New(tt.input))
			program := l.ParseProgram()

			if len(l.Errors()) > 0 {
				t.Fatalf("Parser errors: %v", l.Errors())
			}

			if len(program.Statements) != 1 {
				t.Fatalf("Expected 1 statement, got %d", len(program.Statements))
			}

			stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
			if !ok {
				t.Fatalf("Expected ExpressionStatement, got %T", program.Statements[0])
			}

			actual := stmt.Expression.String()
			if actual != tt.expected {
				t.Errorf("Expected %q, got %q", tt.expected, actual)
			}
		})
	}
}
