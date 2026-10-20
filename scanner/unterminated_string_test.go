package scanner

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/token"
)

func TestUnterminatedStringAtEOFIsIllegal(t *testing.T) {
	for _, input := range []string{`"`, `"hello`, "\"hello\n", `"hello\`, `"hello\"`, `"hello\x`, `"hello\x4`, `"bad\q`} {
		t.Run(input, func(t *testing.T) {
			s := New(input)
			tok := s.NextToken()
			if tok.TokenKind != token.ILLEGAL || tok.Literal != "unclosed string literal: expected closing quote before end of input" {
				t.Fatalf("want unclosed-string ILLEGAL, got %s (%q)", tok.TokenKind, tok.Literal)
			}
			if tok.Line != 1 || tok.Column != 1 || tok.ByteStart != 0 || tok.ByteEnd != len(input) {
				t.Fatalf("wrong unterminated-string source span: %+v", tok)
			}
			if next := s.NextToken(); next.TokenKind != token.EOF || next.ByteStart != len(input) {
				t.Fatalf("expected EOF after unterminated string, got %+v", next)
			}
		})
	}
}

func TestClosedInvalidEscapeKeepsItsDiagnostic(t *testing.T) {
	for _, input := range []string{`"bad\q"`, `"short\x4"`, `"notahex\xZZ"`} {
		tok := New(input).NextToken()
		if tok.TokenKind != token.ILLEGAL || !strings.HasPrefix(tok.Literal, "invalid escape sequence") {
			t.Fatalf("closed invalid escape: got %s (%q)", tok.TokenKind, tok.Literal)
		}
	}
}
