package source

import "testing"

func TestUTF16PositionsAndLinks(t *testing.T) {
	const text = "a😀b\néz\n"
	file := NewFile(1, "src/example.oak", text)

	// b begins after ASCII 'a' (1 UTF-16 unit) and 😀 (2 UTF-16 units).
	pos, err := file.PositionAt(len("a😀"))
	if err != nil {
		t.Fatalf("PositionAt failed: %v", err)
	}
	if pos.Line != 1 || pos.Column != 4 {
		t.Fatalf("expected 1:4, got %d:%d", pos.Line, pos.Column)
	}

	lsp, err := file.LSPPositionAt(len("a😀"))
	if err != nil {
		t.Fatalf("LSPPositionAt failed: %v", err)
	}
	if lsp.Line != 0 || lsp.Character != 3 {
		t.Fatalf("expected LSP 0:3, got %d:%d", lsp.Line, lsp.Character)
	}

	span, err := file.Span(len("a"), len("a😀"))
	if err != nil {
		t.Fatalf("Span failed: %v", err)
	}
	location, err := file.Location(span)
	if err != nil {
		t.Fatalf("Location failed: %v", err)
	}
	if location != "src/example.oak:1:2" {
		t.Fatalf("unexpected location %q", location)
	}

	uri, err := file.VSCodeURI(span)
	if err != nil {
		t.Fatalf("VSCodeURI failed: %v", err)
	}
	if uri != "vscode://file/src/example.oak:1:2" {
		t.Fatalf("unexpected VS Code URI %q", uri)
	}
}

func TestRejectsByteOffsetInsideRune(t *testing.T) {
	file := NewFile(1, "unicode.oak", "😀")
	if _, err := file.LSPPositionAt(1); err == nil {
		t.Fatal("expected offset inside UTF-8 rune to fail")
	}
	if _, err := file.Span(0, 1); err == nil {
		t.Fatal("expected span ending inside UTF-8 rune to fail")
	}
}

func TestMultilinePosition(t *testing.T) {
	file := NewFile(1, "multi.oak", "one\n😀two\n")
	pos, err := file.PositionAt(len("one\n😀"))
	if err != nil {
		t.Fatalf("PositionAt failed: %v", err)
	}
	if pos.Line != 2 || pos.Column != 3 {
		t.Fatalf("expected 2:3, got %d:%d", pos.Line, pos.Column)
	}
}
