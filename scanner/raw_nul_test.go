package scanner

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

func collectRawNULTokens(t *testing.T, input string) []token.Token {
	t.Helper()
	s := New(input)
	var tokens []token.Token
	for i := 0; i <= len(input)+1; i++ {
		tok := s.NextToken()
		if tok.TokenKind != token.TRIVIA {
			tokens = append(tokens, tok)
		}
		if tok.TokenKind == token.EOF {
			if tok.ByteStart != len(input) || tok.ByteEnd != len(input) {
				t.Fatalf("premature EOF at [%d,%d), input length %d", tok.ByteStart, tok.ByteEnd, len(input))
			}
			return tokens
		}
	}
	t.Fatal("scanner failed to reach physical EOF")
	return nil
}

func TestRawNULOutsideTextIsIllegalAndAdvances(t *testing.T) {
	for _, input := range []string{"\x00", "\x00next", "before\x00after", "before\x00", "\x00\x00next\x00", "a\n\x00b"} {
		t.Run(input, func(t *testing.T) {
			if offset, valid := source.ValidateUTF8(input); !valid {
				t.Fatalf("raw NUL remains valid UTF-8, invalid at %d", offset)
			}
			tokens := collectRawNULTokens(t, input)
			illegal := 0
			var identifiers []string
			for _, tok := range tokens {
				switch tok.TokenKind {
				case token.ILLEGAL:
					illegal++
					if tok.Literal != "unexpected NUL character outside string literal or comment" || tok.ByteEnd != tok.ByteStart+1 || input[tok.ByteStart] != 0 {
						t.Fatalf("incorrect raw-NUL diagnostic/span: %+v", tok)
					}
				case token.IDENT:
					identifiers = append(identifiers, tok.Literal)
				}
			}
			if illegal != strings.Count(input, "\x00") {
				t.Fatalf("got %d illegal tokens for %d NULs", illegal, strings.Count(input, "\x00"))
			}
			want := strings.Fields(strings.ReplaceAll(input, "\x00", " "))
			if strings.Join(identifiers, ",") != strings.Join(want, ",") {
				t.Fatalf("identifiers lost after NUL: got %q, want %q", identifiers, want)
			}
		})
	}
}

func TestRawNULStringMatchesEscapedValue(t *testing.T) {
	for _, body := range []string{"\x00", "\x00a", "a\x00b", "a\x00", "\x00a\x00b\x00", "😀\x00\nq"} {
		t.Run(body, func(t *testing.T) {
			for _, spelling := range []string{body, strings.ReplaceAll(body, "\x00", `\0`), strings.ReplaceAll(body, "\x00", `\x00`)} {
				input := `"` + spelling + `" next`
				tokens := collectRawNULTokens(t, input)
				if len(tokens) != 3 || tokens[0].TokenKind != token.STRING || tokens[0].Literal != body || tokens[1].TokenKind != token.IDENT || tokens[1].Literal != "next" {
					t.Fatalf("string bytes or suffix changed for %q: %+v", spelling, tokens)
				}
				if tokens[0].ByteStart != 0 || tokens[0].ByteEnd != len(spelling)+2 {
					t.Fatalf("string span: %+v", tokens[0])
				}
			}
		})
	}
}

func TestRawNULInCommentsPreservesContentAndSuffix(t *testing.T) {
	cases := []struct{ input, comment, suffix string }{
		{"//\x00a\nnext", "\x00a", "next"},
		{"//a\x00b\nnext", "a\x00b", "next"},
		{"//a\x00\nnext", "a\x00", "next"},
		{"//a\x00", "a\x00", ""},
		{"/*\x00a*/next", "\x00a", "next"},
		{"/*a\x00b*/next", "a\x00b", "next"},
		{"/*a\x00*/next", "a\x00", "next"},
		{"/*😀\x00\nq*/next", "😀\x00\nq", "next"},
		// Block comments retain their existing first-closing-delimiter behavior.
		{"/*outer\x00/*inner\x00*/next", "outer\x00/*inner\x00", "next"},
	}
	for _, tc := range cases {
		t.Run(tc.input, func(t *testing.T) {
			tokens := collectRawNULTokens(t, tc.input)
			if tokens[0].TokenKind != token.COMMENT || tokens[0].Literal != tc.comment {
				t.Fatalf("comment content changed: %+v", tokens)
			}
			if tc.suffix != "" && (len(tokens) != 3 || tokens[1].TokenKind != token.IDENT || tokens[1].Literal != tc.suffix) {
				t.Fatalf("comment lost its suffix: %+v", tokens)
			}
			if tc.suffix == "" && len(tokens) != 2 {
				t.Fatalf("unexpected trailing tokens: %+v", tokens)
			}
		})
	}
}

func TestUnterminatedConstructWithRawNULReachesPhysicalEOF(t *testing.T) {
	for _, input := range []string{"\"a\x00b", "\"\x00", "\"a\x00\\", "/*a\x00b", "/*\x00", "/*outer /*inner\x00"} {
		t.Run(input, func(t *testing.T) {
			tokens := collectRawNULTokens(t, input)
			want := "unclosed string literal"
			if strings.HasPrefix(input, "/*") {
				want = "unterminated block comment"
			}
			if len(tokens) != 2 || tokens[0].TokenKind != token.ILLEGAL || !strings.Contains(tokens[0].Literal, want) || tokens[0].ByteEnd != len(input) {
				t.Fatalf("want full-span %s error, got %+v", want, tokens)
			}
		})
	}
}

func TestRawNULAfterBackslashRemainsInvalidEscape(t *testing.T) {
	for _, input := range []string{"\"a\\\x00b\" next", "\"a\\x\x00b\" next", "\"a\\x4\x00b\" next"} {
		tokens := collectRawNULTokens(t, input)
		if len(tokens) != 3 || tokens[0].TokenKind != token.ILLEGAL || !strings.HasPrefix(tokens[0].Literal, "invalid escape sequence") || tokens[1].Literal != "next" {
			t.Fatalf("escape policy or recovery changed: %+v", tokens)
		}
	}
}

func TestRawNULPreservesUTF16Positions(t *testing.T) {
	tokens := collectRawNULTokens(t, "\"😀\"\x00next")
	if len(tokens) != 4 {
		t.Fatalf("unexpected tokens: %+v", tokens)
	}
	nul, next := tokens[1], tokens[2]
	if nul.TokenKind != token.ILLEGAL || nul.Line != 1 || nul.Column != 5 || nul.EndColumn != 6 || nul.ByteStart != 6 || nul.ByteEnd != 7 {
		t.Fatalf("incorrect NUL source position: %+v", nul)
	}
	if next.TokenKind != token.IDENT || next.Column != 6 || next.ByteStart != 7 {
		t.Fatalf("incorrect post-NUL source position: %+v", next)
	}
}
