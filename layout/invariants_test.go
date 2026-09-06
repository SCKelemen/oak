package layout

import (
	"testing"

	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func sourceSignificant(input string) []token.Token {
	return significant(scanner.New(input))
}

func normalizedSignificant(input string) []token.Token {
	return significant(New(scanner.New(input)))
}

func originalTokens(tokens []token.Token) []token.Token {
	out := make([]token.Token, 0, len(tokens))
	for _, tok := range tokens {
		if !tok.Synthetic {
			out = append(out, tok)
		}
	}
	return out
}

func assertOriginalTokensEqual(t *testing.T, want, got []token.Token) {
	t.Helper()
	if len(want) != len(got) {
		t.Fatalf("original token count changed: want=%d got=%d\nwant=%#v\ngot=%#v", len(want), len(got), want, got)
	}
	for i := range want {
		w := want[i]
		g := got[i]
		if w.TokenKind != g.TokenKind ||
			w.Literal != g.Literal ||
			w.Line != g.Line ||
			w.Column != g.Column ||
			w.EndLine != g.EndLine ||
			w.EndColumn != g.EndColumn ||
			w.ByteStart != g.ByteStart ||
			w.ByteEnd != g.ByteEnd {
			t.Fatalf("original token %d changed:\nwant=%#v\ngot =%#v", i, w, g)
		}
		if g.Synthetic {
			t.Fatalf("original token %d became synthetic: %#v", i, g)
		}
	}
}

func assertSyntheticBracesBalanced(t *testing.T, tokens []token.Token) {
	t.Helper()
	depth := 0
	for i, tok := range tokens {
		if !tok.Synthetic {
			continue
		}
		switch tok.TokenKind {
		case token.LBRACE:
			depth++
		case token.RBRACE:
			depth--
			if depth < 0 {
				t.Fatalf("synthetic close at token %d has no matching open", i)
			}
		}
	}
	if depth != 0 {
		t.Fatalf("synthetic braces are unbalanced: remaining depth=%d", depth)
	}
}

func TestNormalizationPreservesOriginalSignificantTokens(t *testing.T) {
	tests := map[string]string{
		"function": `fn answer(): u32
  x := 40
  x + 2
`,
		"nested while": `fn countdown(n: u32): u32
  x := n
  while x > 0
    x = x - 1
  x
`,
		"explicit block": `fn f(): u32 {
  x := 1
  x
}
`,
		"expression body": `fn add(a: u32, b: u32): u32 = a + b
`,
		"multiline parameters": `fn add(
  a: u32,
  b: u32,
): u32
  a + b
`,
		"unsafe body": `fn f(): u32
  unsafe
    x := 1
    x
`,
	}

	for name, input := range tests {
		t.Run(name, func(t *testing.T) {
			want := sourceSignificant(input)
			got := originalTokens(normalizedSignificant(input))
			assertOriginalTokensEqual(t, want, got)
		})
	}
}

func TestNormalizationBalancesSyntheticBraces(t *testing.T) {
	tests := map[string]string{
		"empty function body shape": `fn f(): u32
  x
`,
		"nested while": `fn f(): u32
  x := 2
  while x > 0
    x = x - 1
  x
`,
		"multiple dedents": `fn f(): u32
  while true
    while true
      x := 1
    x
  x
`,
		"explicit block": `fn f(): u32 {
  x
}
`,
		"expression body": `fn f(): u32 = 1
`,
		"multiline parameters": `fn add(
  a: u32,
  b: u32,
): u32
  a + b
`,
	}

	for name, input := range tests {
		t.Run(name, func(t *testing.T) {
			assertSyntheticBracesBalanced(t, normalizedSignificant(input))
		})
	}
}

func TestSyntheticBracesAreZeroWidth(t *testing.T) {
	input := `fn f(): u32
  while true
    x := 1
  x
`
	for _, tok := range normalizedSignificant(input) {
		if !tok.Synthetic || (tok.TokenKind != token.LBRACE && tok.TokenKind != token.RBRACE) {
			continue
		}
		if tok.ByteStart != tok.ByteEnd {
			t.Fatalf("synthetic brace has non-zero byte width: %#v", tok)
		}
		if tok.Line != tok.EndLine || tok.Column != tok.EndColumn {
			t.Fatalf("synthetic brace has non-zero source range: %#v", tok)
		}
	}
}
