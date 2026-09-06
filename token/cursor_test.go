package token_test

import (
	"testing"

	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

func TestCursorPeekDoesNotConsume(t *testing.T) {
	file := source.NewFile(3, "cursor.oak", "a b c")
	cursor := token.NewCursor(scanner.NewFile(file))

	if got := cursor.Peek(0); got.TokenKind != token.IDENT || got.Literal != "a" {
		t.Fatalf("unexpected first peek: %#v", got)
	}
	if got := cursor.Peek(2); got.TokenKind != token.IDENT || got.Literal != "b" {
		// Raw offset 1 is trivia, so raw offset 2 is b.
		t.Fatalf("unexpected third raw token: %#v", got)
	}
	if got := cursor.NextToken(); got.Literal != "a" {
		t.Fatalf("peek consumed input; next=%q", got.Literal)
	}
	if cursor.SourceFile() != file {
		t.Fatal("cursor did not preserve source identity")
	}
}

func TestCursorCanResetWithinBufferedInput(t *testing.T) {
	cursor := token.NewCursor(scanner.New("a b"))
	mark := cursor.Mark()
	first := cursor.NextToken()
	_ = cursor.NextToken() // trivia
	second := cursor.NextToken()
	if first.Literal != "a" || second.Literal != "b" {
		t.Fatalf("unexpected tokens %q %q", first.Literal, second.Literal)
	}
	if err := cursor.Reset(mark); err != nil {
		t.Fatalf("Reset failed: %v", err)
	}
	if got := cursor.NextToken(); got.Literal != "a" {
		t.Fatalf("expected replayed a, got %q", got.Literal)
	}
}
