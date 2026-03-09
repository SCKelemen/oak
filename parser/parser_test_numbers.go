package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestIntegerLiteralOverflowProducesClearError(t *testing.T) {
	input := "9223372036854775808;"

	p := New(scanner.New(input))
	_ = p.ParseProgram()

	errs := p.Errors()
	if len(errs) == 0 {
		t.Fatalf("expected parser error for overflowing integer literal")
	}
	if !strings.Contains(errs[0], "out of range") {
		t.Fatalf("expected out-of-range error, got %q", errs[0])
	}
}

func TestInvalidRadixLiteralProducesSpecificErrors(t *testing.T) {
	tests := []struct {
		name        string
		input       string
		containsMsg string
	}{
		{
			name:        "missing digits",
			input:       "16r;",
			containsMsg: "missing digits",
		},
		{
			name:        "leading separator",
			input:       "16r_F;",
			containsMsg: "at the beginning",
		},
		{
			name:        "consecutive separators",
			input:       "16rF__2;",
			containsMsg: "consecutive digit separators",
		},
		{
			name:        "trailing separator",
			input:       "16rF_;",
			containsMsg: "at the end",
		},
		{
			name:        "digit outside radix",
			input:       "16rG;",
			containsMsg: "invalid digits for radix 16",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			p := New(scanner.New(tt.input))
			_ = p.ParseProgram()

			errs := p.Errors()
			if len(errs) == 0 {
				t.Fatalf("expected parser error for %q", tt.input)
			}
			joined := strings.Join(errs, "\n")
			if !strings.Contains(joined, tt.containsMsg) {
				t.Fatalf("expected error containing %q, got %q", tt.containsMsg, joined)
			}
		})
	}
}

func TestUnicodeRadixLiteralParsesToExpectedValue(t *testing.T) {
	input := "١٦rF_٢;"

	p := New(scanner.New(input))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("unexpected parser errors: %v", p.Errors())
	}
	if len(program.Statements) != 1 {
		t.Fatalf("expected one statement, got %d", len(program.Statements))
	}

	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok {
		t.Fatalf("expected expression statement, got %T", program.Statements[0])
	}
	intLit, ok := stmt.Expression.(*ast.IntegerLiteral)
	if !ok {
		t.Fatalf("expected integer literal, got %T", stmt.Expression)
	}
	if intLit.Value != 242 {
		t.Fatalf("expected 242, got %d", intLit.Value)
	}
}

func TestRadixLiteralOverflowProducesClearError(t *testing.T) {
	input := "16rFFFFFFFFFFFFFFFFF;"

	p := New(scanner.New(input))
	_ = p.ParseProgram()

	errs := p.Errors()
	if len(errs) == 0 {
		t.Fatalf("expected parser error for overflowing radix literal")
	}
	joined := strings.Join(errs, "\n")
	if !strings.Contains(joined, "out of range") {
		t.Fatalf("expected out-of-range radix error, got %q", joined)
	}
}
