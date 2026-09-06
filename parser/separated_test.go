package parser

import (
	"testing"

	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestParseSeparatedGenericMethod(t *testing.T) {
	p := New(scanner.New("(alpha, beta, gamma)"))
	if !p.currentTokenIs(token.LPAREN) {
		t.Fatalf("expected opening paren, got %s", p.currentToken.TokenKind)
	}

	items, ok := p.parseSeparated(token.RPAREN, token.COMMA, false, func() (string, bool) {
		if !p.currentTokenIs(token.IDENT) {
			p.addErrorAtCurrentToken("expected identifier")
			return "", false
		}
		return p.currentToken.Literal, true
	})
	if !ok {
		t.Fatalf("parseSeparated failed: %v", p.Errors())
	}

	want := []string{"alpha", "beta", "gamma"}
	if len(items) != len(want) {
		t.Fatalf("expected %d items, got %d", len(want), len(items))
	}
	for i := range want {
		if items[i] != want[i] {
			t.Fatalf("item %d: expected %q, got %q", i, want[i], items[i])
		}
	}
	if !p.currentTokenIs(token.RPAREN) {
		t.Fatalf("expected parser to finish on closing paren, got %s", p.currentToken.TokenKind)
	}
}

func TestParseSeparatedAllowsEmptyAndOptionalTrailingSeparator(t *testing.T) {
	empty := New(scanner.New("()"))
	items, ok := empty.parseSeparated(token.RPAREN, token.COMMA, false, func() (string, bool) {
		return empty.currentToken.Literal, true
	})
	if !ok || len(items) != 0 {
		t.Fatalf("expected empty sequence, got %v, ok=%v", items, ok)
	}

	trailing := New(scanner.New("(a, b,)"))
	items, ok = trailing.parseSeparated(token.RPAREN, token.COMMA, true, func() (string, bool) {
		if !trailing.currentTokenIs(token.IDENT) {
			return "", false
		}
		return trailing.currentToken.Literal, true
	})
	if !ok || len(items) != 2 || items[0] != "a" || items[1] != "b" {
		t.Fatalf("unexpected trailing-separator result: %v, ok=%v", items, ok)
	}
}
