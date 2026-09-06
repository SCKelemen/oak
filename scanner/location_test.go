package scanner

import (
	"testing"

	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

func TestScannerTracksUTF16ColumnsAndExactEnds(t *testing.T) {
	file := source.NewFile(7, "unicode.oak", "\"😀\" value")
	s := NewFile(file)

	str := s.NextToken()
	if str.TokenKind != token.STRING {
		t.Fatalf("expected STRING, got %s", str.TokenKind)
	}
	if str.Line != 1 || str.Column != 1 || str.EndLine != 1 || str.EndColumn != 5 {
		t.Fatalf("unexpected string range %d:%d-%d:%d", str.Line, str.Column, str.EndLine, str.EndColumn)
	}
	if str.ByteStart != 0 || str.ByteEnd != len("\"😀\"") {
		t.Fatalf("unexpected byte span [%d,%d)", str.ByteStart, str.ByteEnd)
	}

	trivia := s.NextToken()
	if trivia.TokenKind != token.TRIVIA {
		t.Fatalf("expected TRIVIA, got %s", trivia.TokenKind)
	}

	ident := s.NextToken()
	if ident.TokenKind != token.IDENT || ident.Column != 6 {
		t.Fatalf("expected identifier at UTF-16 column 6, got %s at %d", ident.TokenKind, ident.Column)
	}
	if s.SourceFile() != file {
		t.Fatal("scanner did not preserve source identity")
	}
}

func TestScannerTracksMultilineCommentEnd(t *testing.T) {
	s := New("/* a\n😀 */x")
	comment := s.NextToken()
	if comment.TokenKind != token.COMMENT {
		t.Fatalf("expected COMMENT, got %s", comment.TokenKind)
	}
	if comment.Line != 1 || comment.Column != 1 || comment.EndLine != 2 || comment.EndColumn != 6 {
		t.Fatalf("unexpected comment range %d:%d-%d:%d", comment.Line, comment.Column, comment.EndLine, comment.EndColumn)
	}
	ident := s.NextToken()
	if ident.TokenKind != token.IDENT || ident.Line != 2 || ident.Column != 6 {
		t.Fatalf("expected x at 2:6, got %s at %d:%d", ident.TokenKind, ident.Line, ident.Column)
	}
}
