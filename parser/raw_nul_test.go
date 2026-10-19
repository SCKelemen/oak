package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestParserRawNULRejectsAndRetainsFollowingStatements(t *testing.T) {
	for _, input := range []string{"\x00a := true", "a := true\x00b := false", "a := true\x00", "\x00a := true\x00b := false\x00"} {
		for _, normalized := range []bool{false, true} {
			var src token.Source = scanner.New(input)
			if normalized {
				src = layout.New(src)
			}
			p := New(src)
			program := p.ParseProgram()
			if len(program.Statements) != strings.Count(input, ":=") {
				t.Fatalf("layout=%v: statements dropped after NUL in %q: %d", normalized, input, len(program.Statements))
			}
			if len(p.Errors()) != strings.Count(input, "\x00") {
				t.Fatalf("layout=%v: expected one error per NUL: %v", normalized, p.Errors())
			}
			for _, err := range p.Errors() {
				if !strings.Contains(err, "unexpected NUL character") {
					t.Fatalf("unexpected diagnostic: %s", err)
				}
			}
		}
	}
}

func TestParserRawNULInsideTextPreservesSuffix(t *testing.T) {
	for _, input := range []string{"s := \"a\x00b\"; next := true", "//a\x00b\nnext := true", "/*a\x00b*/next := true", "/*outer\x00/*inner\x00*/next := true", "f: (): string\n  //a\x00b\n  \"a\x00b\"\nnext := true"} {
		p := New(layout.New(scanner.New(input)))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			t.Fatalf("text NUL in %q: %v", input, errs)
		}
		last := program.Statements[len(program.Statements)-1]
		decl, ok := last.(*ast.VariableDeclaration)
		if !ok || decl.Name.Value != "next" {
			t.Fatalf("suffix was not preserved: %T", last)
		}
		if strings.HasPrefix(input, "s :=") {
			value := program.Statements[0].(*ast.VariableDeclaration).Value.(*ast.StringLiteral).Value
			if value != "a\x00b" {
				t.Fatalf("raw NUL string decoded as %q", value)
			}
		}
	}
}
