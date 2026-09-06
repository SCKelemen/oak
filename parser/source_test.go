package parser

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

type sliceTokenSource struct {
	tokens []token.Token
	index  int
}

func (s *sliceTokenSource) NextToken() token.Token {
	if s.index >= len(s.tokens) {
		return token.Token{TokenKind: token.EOF}
	}
	tok := s.tokens[s.index]
	s.index++
	return tok
}

func TestParserConsumesTokenSourceDirectly(t *testing.T) {
	source := &sliceTokenSource{tokens: []token.Token{
		{TokenKind: token.INT, Literal: "1", Line: 1, Column: 1},
		{TokenKind: token.SUM, Literal: "+", Line: 1, Column: 3},
		{TokenKind: token.INT, Literal: "2", Line: 1, Column: 5},
		{TokenKind: token.EOF, Line: 1, Column: 6},
	}}

	p := New(source)
	program := p.ParseProgram()

	if errors := p.Errors(); len(errors) != 0 {
		t.Fatalf("unexpected parser errors: %v", errors)
	}
	if len(program.Statements) != 1 {
		t.Fatalf("expected one statement, got %d", len(program.Statements))
	}
	if source.index == 0 {
		t.Fatal("parser did not consume the provided token source")
	}
}
