package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestExplicitInitializerRequiresExpression(t *testing.T) {
	for _, head := range []string{
		"x: i32", "x", "_", "a[0]",
		"f: (): i32", "f(): i32", "fn f(): i32", "f := fn(): i32",
	} {
		input := head + " = ; sentinel := 7"
		t.Run(input, func(t *testing.T) {
			for _, normalize := range []bool{false, true} {
				var source token.Source = scanner.New(input)
				if normalize {
					source = layout.New(source)
				}
				p := New(source)
				program := p.ParseProgram()
				found := false
				for _, d := range p.Diagnostics() {
					if d.Message == "expected value expression after =" && d.Range.Start.Line == 0 && d.Range.Start.Character == len(head)+1 {
						found = true
					}
				}
				if !found {
					t.Errorf("layout=%v: missing positioned initializer diagnostic: %v", normalize, p.Errors())
				}
				if len(program.Statements) == 0 {
					t.Fatalf("layout=%v: recovery lost all statements", normalize)
				}
				last, ok := program.Statements[len(program.Statements)-1].(*ast.VariableDeclaration)
				if !ok || last.Name.Value != "sentinel" {
					t.Fatalf("layout=%v: recovery lost following declaration", normalize)
				}
			}
		})
	}
}

func TestExplicitInitializerCompatibilityHandler(t *testing.T) {
	p := New(scanner.New("x: i32 = ;"))
	if got := p.parseVariableDeclaration(); !strings.Contains(strings.Join(p.Errors(), "\n"), "expected value expression after =") {
		t.Fatalf("compatibility declaration accepted missing initializer: %#v, %v", got, p.Errors())
	}
}

func TestExplicitInitializerNestedAndExistingErrors(t *testing.T) {
	for _, input := range []string{
		"fn f(): i32 { x: i32 = ; x }", "fn f(): i32 { x: i32 = }",
		"fn f(): i32 { x: i32; x = ; x }", "fn f(): () { _ = ; }",
		"fn f(): () { a[0] = ; }", "x: i32 = ,", "x: i32 = )", "x: i32 = ]",
		"x: i32 = :", "x: i32 = := 1", "x: i32 =", "f: (): i32 =",
		"x: i32 = 1 + ;", "x: i32 = 1 |> ;", "x: i32 = \x00;", `x: string = "unclosed`,
	} {
		t.Run(input, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			p.ParseProgram()
			if len(p.Errors()) == 0 {
				t.Fatal("missing initializer accepted without diagnostic")
			}
		})
	}
}

func TestExplicitInitializerPreservesOptionalForms(t *testing.T) {
	for _, input := range []string{
		"x: i32", "fn f(): i32 { x: i32; x }", "f: (): i32",
		"x: i32 = 1", "x = 1", "_ = 1", "a[0] = 1",
		"f: (): i32 = 1", "f(): i32 = 1", "fn f(): i32 = 1", "f := fn(): i32 = 1",
		"f: (): () = {}", "f(): () = {}", "fn f(): () = {}", "f := fn(): () = {}",
		"x: T = {}", "x: T = []", "x = {}", "_ = []", "a[0] = {}", "x: T = f()",
		"x: T = a[:]", "x: T = a[:2]", "x: T = a[1:]", "x: T = a[1:2]",
		"fn f(): () {}", "fn f(): () { return }", "true ? {} | {}",
		"fn f(): i32\n  x: i32\n  x", "x: i32 = 1 /*\x00*/ + 2", "s: string = \"a\x00b\"",
	} {
		t.Run(input, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			program := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("valid control: %v", p.Errors())
			}
			if len(program.Statements) == 0 {
				t.Fatal("valid source dropped")
			}
			_ = program.String()
		})
	}
}

func TestExplicitInitializerOtherEqualsGrammarRejects(t *testing.T) {
	for _, input := range []string{
		"Name: type = ;", "type Name: type = ;", "Reader: interface = ;",
		"json: tag = ;", "Name: protocol = ;", "Name: literals = ;",
		"Name: type = | V: i32 = ;", "Signature: type = { Key: type = ; }",
		"P: protocol = { fact F = ; }",
	} {
		t.Run(input, func(t *testing.T) {
			p := New(layout.New(scanner.New(input)))
			p.ParseProgram()
			if len(p.Errors()) == 0 {
				t.Fatal("mandatory non-expression equals grammar accepted empty body")
			}
		})
	}
}
