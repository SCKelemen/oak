package scanner

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

func TestNextToken(t *testing.T) {
	input := "[]{}(),.;:=|&"
	tests := []struct {
		expectedKind    token.TokenKind
		expectedLiteral string
	}{
		{token.LBRACK, "["},
		{token.RBRACK, "]"},
		{token.LBRACE, "{"},
		{token.RBRACE, "}"},
		{token.LPAREN, "("},
		{token.RPAREN, ")"},
		{token.COMMA, ","},
		{token.DOT, "."},
		{token.SEMI, ";"},
		{token.COLON, ":"},
		{token.EQL, "="},
		{token.PIPE, "|"},
		{token.AMP, "&"},
		{token.EOF, ""},
	}

	scnr := New(input)
	for i, tt := range tests {
		tok := scnr.NextToken()
		if tok.TokenKind != tt.expectedKind {
			t.Fatalf("tests[%d] - tokenKind wrong. expected=%q, got=%q",
				i, tt.expectedKind, tok.TokenKind)
		}

		if tok.Literal != tt.expectedLiteral {
			t.Fatalf("tests[%d] - literal wrong. expected=%q, got=%q",
				i, tt.expectedLiteral, tok.Literal)
		}
	}
}

func TestScanKeyword(t *testing.T) {
	input := "type"
	tests := []struct {
		expectedKind    token.TokenKind
		expectedLiteral string
	}{
		{token.TYPE, "type"},
		{token.EOF, ""},
	}

	scnr := New(input)
	for i, tt := range tests {
		tok := scnr.NextToken()
		if tok.TokenKind != tt.expectedKind {
			t.Fatalf("tests[%d] - tokenKind wrong. expected=%q, got=%q",
				i, tt.expectedKind, tok.TokenKind)
		}

		if tok.Literal != tt.expectedLiteral {
			t.Fatalf("tests[%d] - literal wrong. expected=%q, got=%q",
				i, tt.expectedLiteral, tok.Literal)
		}
	}
}
func TestScanKeywordWithExtraNoise(t *testing.T) {
	input := "type.keyWord"
	tests := []struct {
		expectedKind    token.TokenKind
		expectedLiteral string
	}{
		{token.TYPE, "type"},
		{token.DOT, "."},
		{token.IDENT, "keyWord"},
		{token.EOF, ""},
	}

	scnr := New(input)
	for i, tt := range tests {
		tok := scnr.NextToken()
		if tok.TokenKind != tt.expectedKind {
			t.Fatalf("tests[%d] - tokenKind wrong. expected=%q, got=%q",
				i, tt.expectedKind, tok.TokenKind)
		}

		if tok.Literal != tt.expectedLiteral {
			t.Fatalf("tests[%d] - literal wrong. expected=%q, got=%q",
				i, tt.expectedLiteral, tok.Literal)
		}
	}
}

func TestScanShortExampleProgram(t *testing.T) {
	input := `
	type ReaderWriterCloser
		= Reader
		& Writer
		& Closer
	`
	tests := []struct {
		expectedKind    token.TokenKind
		expectedLiteral string
	}{
		{token.TYPE, "type"},
		{token.IDENT, "ReaderWriterCloser"},
		{token.EQL, "="},
		{token.IDENT, "Reader"},
		{token.AMP, "&"},
		{token.IDENT, "Writer"},
		{token.AMP, "&"},
		{token.IDENT, "Closer"},
		{token.EOF, ""},
	}

	scnr := New(input)
	for i, tt := range tests {
		tok := scnr.NextToken()
		if tok.TokenKind != tt.expectedKind {
			t.Fatalf("tests[%d] - tokenKind wrong. expected=%q, got=%q",
				i, tt.expectedKind, tok.TokenKind)
		}

		if tok.Literal != tt.expectedLiteral {
			t.Fatalf("tests[%d] - literal wrong. expected=%q, got=%q",
				i, tt.expectedLiteral, tok.Literal)
		}
	}
}
