package scanner

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

// String literal escapes (docs/spec/10-syntax.md section 2a) are decoded by
// the scanner exactly once; the literal's bytes are what the program means.
func TestStringLiteralEscapes(t *testing.T) {
	tests := []struct {
		name  string
		input string
		want  string
	}{
		{"plain", `"hello"`, "hello"},
		{"newline and tab", `"a\tb\n"`, "a\tb\n"},
		{"carriage return", `"a\rb"`, "a\rb"},
		{"backslash", `"a\\b"`, `a\b`},
		{"quote", `"say \"hi\""`, `say "hi"`},
		{"nul", `"a\0b"`, "a\x00b"},
		{"hex byte", `"\x41\x7a"`, "Az"},
		{"hex upper", `"\xFF"`, "\xff"},
		{"utf8 passes through", `"héllo 😀"`, "héllo 😀"},
		{"escaped quote does not terminate", `"a\"" x`, `a"`},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			tok := New(tt.input).NextToken()
			if tok.TokenKind != token.STRING {
				t.Fatalf("expected STRING, got %s (%q)", tok.TokenKind, tok.Literal)
			}
			if tok.Literal != tt.want {
				t.Fatalf("literal = %q, want %q", tok.Literal, tt.want)
			}
		})
	}
}

// An unknown escape is an ILLEGAL token, and the literal is still consumed to
// its closing quote so the following tokens scan normally.
func TestInvalidStringEscapeIsIllegal(t *testing.T) {
	for _, input := range []string{`"bad\q" next`, `"short\x4" next`, `"notahex\xZZ" next`} {
		s := New(input)
		tok := s.NextToken()
		if tok.TokenKind != token.ILLEGAL {
			t.Fatalf("%q: expected ILLEGAL, got %s (%q)", input, tok.TokenKind, tok.Literal)
		}
		next := s.NextToken()
		for next.TokenKind == token.TRIVIA {
			next = s.NextToken()
		}
		if next.TokenKind != token.IDENT || next.Literal != "next" {
			t.Fatalf("%q: scanning must resume after the literal, got %s (%q)", input, next.TokenKind, next.Literal)
		}
	}
}
