package parser

import (
	"testing"

	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
)

func TestParserPreservesSourceFileAndBuildsLinks(t *testing.T) {
	file := source.NewFile(9, "src/main.oak", "😀value")
	p := New(layout.New(scanner.NewFile(file)))

	if p.SourceFile() != file {
		t.Fatal("parser did not preserve source identity through layout normalization")
	}

	tok := token.Token{ByteStart: len("😀"), ByteEnd: len("😀value")}
	location, err := p.Location(tok)
	if err != nil {
		t.Fatalf("Location failed: %v", err)
	}
	if location != "src/main.oak:1:3" {
		t.Fatalf("unexpected location %q", location)
	}

	uri, err := p.VSCodeURI(tok)
	if err != nil {
		t.Fatalf("VSCodeURI failed: %v", err)
	}
	if uri != "vscode://file/src/main.oak:1:3" {
		t.Fatalf("unexpected VS Code URI %q", uri)
	}
}
