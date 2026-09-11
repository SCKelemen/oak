package layout

import (
	"testing"

	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func significant(source Source) []token.Token {
	var result []token.Token
	for {
		tok := source.NextToken()
		if tok.TokenKind != token.TRIVIA && tok.TokenKind != token.COMMENT {
			result = append(result, tok)
		}
		if tok.TokenKind == token.EOF {
			return result
		}
	}
}

func kinds(tokens []token.Token) []token.TokenKind {
	out := make([]token.TokenKind, len(tokens))
	for i, tok := range tokens {
		out[i] = tok.TokenKind
	}
	return out
}

func assertKindsEqual(t *testing.T, a, b []token.Token) {
	t.Helper()
	ak := kinds(a)
	bk := kinds(b)
	if len(ak) != len(bk) {
		t.Fatalf("token length differs:\nlayout:   %v\nexplicit: %v", ak, bk)
	}
	for i := range ak {
		if ak[i] != bk[i] {
			t.Fatalf("token %d differs: layout=%s explicit=%s\nlayout:   %v\nexplicit: %v", i, ak[i], bk[i], ak, bk)
		}
	}
}

func TestFunctionLayoutEqualsExplicitBlock(t *testing.T) {
	layoutSource := `fn answer(): u32
  x := 40
  x + 2
`
	explicitSource := `fn answer(): u32 {
  x := 40
  x + 2
}`

	got := significant(New(scanner.New(layoutSource)))
	want := significant(New(scanner.New(explicitSource)))
	assertKindsEqual(t, got, want)

	if got[6].TokenKind != token.LBRACE || !got[6].Synthetic {
		t.Fatalf("expected synthetic opening brace, got %#v", got[6])
	}
	if got[len(got)-2].TokenKind != token.RBRACE || !got[len(got)-2].Synthetic {
		t.Fatalf("expected synthetic closing brace, got %#v", got[len(got)-2])
	}
}

func TestNestedWhileLayoutEqualsExplicitBlocks(t *testing.T) {
	layoutSource := `fn countdown(n: u32): u32
  x := n
  while x > 0
    x = x - 1
  x
`
	explicitSource := `fn countdown(n: u32): u32 {
  x := n
  while x > 0 {
    x = x - 1
  }
  x
}`

	got := significant(New(scanner.New(layoutSource)))
	want := significant(New(scanner.New(explicitSource)))
	assertKindsEqual(t, got, want)
}

func TestExpressionBodiedFunctionDoesNotOpenLayoutBlock(t *testing.T) {
	source := `fn add(a: u32, b: u32): u32 = a + b
`
	tokens := significant(New(scanner.New(source)))
	for _, tok := range tokens {
		if tok.Synthetic && (tok.TokenKind == token.LBRACE || tok.TokenKind == token.RBRACE) {
			t.Fatalf("expression-bodied function synthesized block token: %#v", tok)
		}
	}
}

func TestMultilineParametersDoNotOpenLayoutBlock(t *testing.T) {
	source := `fn add(
  a: u32,
  b: u32,
): u32
  a + b
`
	tokens := significant(New(scanner.New(source)))

	opens := 0
	closes := 0
	for _, tok := range tokens {
		if tok.Synthetic && tok.TokenKind == token.LBRACE {
			opens++
		}
		if tok.Synthetic && tok.TokenKind == token.RBRACE {
			closes++
		}
	}
	if opens != 1 || closes != 1 {
		t.Fatalf("expected one virtual block, got opens=%d closes=%d", opens, closes)
	}
}

func TestDedentClosesNestedBlockBeforeOuterStatement(t *testing.T) {
	source := `fn f(): u32
  x := 2
  while x > 0
    x = x - 1
  x
`
	tokens := significant(New(scanner.New(source)))

	for i := 0; i+1 < len(tokens); i++ {
		if tokens[i].Synthetic && tokens[i].TokenKind == token.RBRACE && tokens[i+1].Literal == "x" {
			return
		}
	}
	t.Fatal("expected nested virtual block to close before outer x expression")
}
