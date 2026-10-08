package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/scanner"
)

// := never chooses a type declaration from the spelling or capitalization
// of its initializer. Type names are ordinary identifier expressions here;
// deciding whether an expression is a value belongs to the checker.
func TestInferredDeclarationsAreValues(t *testing.T) {
	for _, source := range []string{
		"mask := a | b",
		"Color := Red | Blue | Green",
		"mask := a | (b & c)",
		"mask := a | b + c",
		"mask := (a | b)",
		"mask := a | 2",
		"mask := a | next()",
		"mask := pkg.a | pkg.b",
		"mask := flags[0] | flags[1]",
		"mask := 1 | 2",
		"mask := a | b;",
		"alias := u32",
		"kind := type",
	} {
		t.Run(source, func(t *testing.T) {
			p := New(scanner.New(source))
			program := p.ParseProgram()
			if errors := p.Errors(); len(errors) != 0 {
				t.Fatal(errors)
			}
			if len(program.Statements) != 1 {
				t.Fatalf("got %d statements, want one", len(program.Statements))
			}
			decl, ok := program.Statements[0].(*ast.VariableDeclaration)
			if !ok || decl.Type != nil || decl.Value == nil {
				t.Fatalf("want inferred value declaration, got %#v", program.Statements[0])
			}
			if strings.Contains(source, "|") {
				_, ok := decl.Value.(*ast.InfixExpression)
				if !ok || !strings.Contains(decl.Value.String(), " | ") {
					t.Fatalf("want bitwise-or initializer, got %#v", decl.Value)
				}
			}
		})
	}
}

func TestInferredValueOrPrecedence(t *testing.T) {
	p := New(scanner.New("mask := a | b & c ^ d << 1"))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		t.Fatal(errors)
	}
	decl := program.Statements[0].(*ast.VariableDeclaration)
	if got, want := decl.Value.String(), "((a | (b & c)) ^ (d << 1))"; got != want {
		t.Fatalf("initializer = %s, want %s", got, want)
	}
}

func TestInferredValueDiagnostics(t *testing.T) {
	for _, source := range []string{"mask :=", "mask := ;", "f: (): () { mask := }"} {
		p := New(scanner.New(source))
		p.ParseProgram()
		if got := strings.Join(p.Errors(), "\n"); !strings.Contains(got, "expected value expression after :=") {
			t.Errorf("%q: missing initializer diagnostic: %s", source, got)
		}
	}

	p := New(scanner.New("Color := | Red | Blue"))
	p.ParseProgram()
	if got := strings.Join(p.Errors(), "\n"); !strings.Contains(got, "declare an ADT with Name: type = | Variant | ...") {
		t.Fatalf("missing explicit-type migration diagnostic: %s", got)
	}
	first := p.Diagnostics()[0]
	if first.Code != string(diagnostic.CodeParserGeneric) || first.Range.Start.Line != 0 || first.Range.Start.Character != 6 {
		t.Fatalf("migration diagnostic must point to :=: %#v", first)
	}

	for _, source := range []string{"Color := Red | Blue: u32", "mask := a |"} {
		p := New(scanner.New(source))
		program := p.ParseProgram()
		if len(p.Errors()) == 0 {
			t.Errorf("invalid value initializer accepted: %s", source)
		}
		for _, stmt := range program.Statements {
			if _, ok := stmt.(*ast.ADTType); ok {
				t.Errorf("invalid value initializer became a type: %s", source)
			}
		}
	}
}
