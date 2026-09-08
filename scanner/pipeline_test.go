package scanner

import (
	"testing"
	"github.com/SCKelemen/oak/token"
)

func TestPipelineToken(t *testing.T) {
	s := New("value |> f")
	want := []token.TokenKind{token.IDENT, token.TRIVIA, token.PIPE_FORWARD, token.TRIVIA, token.IDENT, token.EOF}
	for i, kind := range want {
		if got := s.NextToken(); got.TokenKind != kind {
			t.Fatalf("token %d = %s (%q), want %s", i, got.TokenKind, got.Literal, kind)
		}
	}
}
