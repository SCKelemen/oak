package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"testing"
)

func TestIdentifierFirstInterfaceDeclaration(t *testing.T) {
	for _, source := range []string{
		"Reader: interface = fn (self) read(buf: [*]Byte) -> Result[u32, Error]",
		"Reader[T]: interface = fn (self: T) read(buf: [*]Byte) -> Result[u32, Error]",
	} {
		parse := func(text string) *ast.InterfaceType {
			t.Helper()
			p := New(scanner.New(text))
			tree := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("%s: %v", text, p.Errors())
			}
			decl, ok := tree.Statements[0].(*ast.InterfaceType)
			if !ok {
				t.Fatalf("want interface, got %T", tree.Statements[0])
			}
			return decl
		}
		canonical, legacy := parse(source), parse("interface "+source)
		if canonical.String() != legacy.String() {
			t.Fatalf("declarations differ: %s / %s", canonical.String(), legacy.String())
		}
		round := parse(canonical.String())
		if round.String() != canonical.String() {
			t.Fatalf("interface roundtrip: %s", round.String())
		}
	}
}

func TestPublicInterfacePrintingPreservesVisibility(t *testing.T) {
	source := "pub Reader: interface = fn (self) read() -> u32"
	p := New(scanner.New(source))
	tree := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatal(p.Errors())
	}
	original := tree.Statements[0].(*ast.InterfaceType)
	q := New(scanner.New(original.String()))
	round := q.ParseProgram()
	if len(q.Errors()) != 0 {
		t.Fatal(q.Errors())
	}
	if !round.Statements[0].(*ast.InterfaceType).Exported {
		t.Fatalf("lost visibility: %s", original.String())
	}
}
