package scanner

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

// Floating-point literals (docs/spec/20-types.md section 11.3.2): a fraction
// or an exponent makes the literal FLOAT; integers, radix forms, and member
// access after an integer stay as they were.
func TestFloatLiterals(t *testing.T) {
	tests := []struct {
		input string
		kind  token.TokenKind
		lit   string
	}{
		{"1.5", token.FLOAT, "1.5"},
		{"2.0e-5", token.FLOAT, "2.0e-5"},
		{"1e3", token.FLOAT, "1e3"},
		{"7E+2", token.FLOAT, "7E+2"},
		{"1_000.5", token.FLOAT, "1000.5"},
		{"0.0", token.FLOAT, "0.0"},
		{"42", token.INT, "42"},
		{"0xFF", token.INT, "16rFF"},
		{"16rFF", token.INT, "16rFF"},
		// Hexadecimal floating-point literals (C99 6.4.4.2): exact.
		{"0x1.8p1", token.FLOAT, "0x1.8p1"},
		{"0x1p-126", token.FLOAT, "0x1p-126"},
		{"0x1P+3", token.FLOAT, "0x1P+3"},
		{"0xA.Fp0", token.FLOAT, "0xA.Fp0"},
		{"0x1_0p1", token.FLOAT, "0x10p1"},
	}
	for _, tt := range tests {
		tok := New(tt.input).NextToken()
		if tok.TokenKind != tt.kind || tok.Literal != tt.lit {
			t.Errorf("%q: got %s %q, want %s %q", tt.input, tok.TokenKind, tok.Literal, tt.kind, tt.lit)
		}
	}
}

func TestIntegerFollowedByDotIsNotAFloat(t *testing.T) {
	s := New("xs[0].x")
	var kinds []token.TokenKind
	for {
		tok := s.NextToken()
		if tok.TokenKind == token.EOF {
			break
		}
		if tok.TokenKind == token.TRIVIA {
			continue
		}
		kinds = append(kinds, tok.TokenKind)
	}
	want := []token.TokenKind{token.IDENT, token.LBRACK, token.INT, token.RBRACK, token.DOT, token.IDENT}
	if len(kinds) != len(want) {
		t.Fatalf("kinds = %v, want %v", kinds, want)
	}
	for i := range want {
		if kinds[i] != want[i] {
			t.Fatalf("kinds = %v, want %v", kinds, want)
		}
	}
}
