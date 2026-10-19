package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestDeclarationContractRejectsLostBinders(t *testing.T) {
	tests := []struct{ name, source, diagnostic string }{
		{"value", "x[T]: i32 = 7", "value declarations do not support type parameters"},
		{"function_value", "f[T]: (i32) -> i32 = identity", "value declarations do not support type parameters"},
		{"tag", "json[T]: tag = { name: string }", "tag declarations do not support type parameters"},
		{"protocol", "P[T]: protocol = { initial A\n tick: A -> A }", "protocol declarations do not support type parameters"},
		{"literals", "L[T]: literals = { \"abc\" }", "literals declarations do not support type parameters"},
		{"dual_adt", "Box[T]: type[U] = | Wrap: U", "but not both"},
		{"duplicate_adt", "Box[T]: type[T] = | Wrap: T", "but not both"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			p := New(scanner.New(tt.source))
			p.ParseProgram()
			if !strings.Contains(strings.Join(p.Errors(), "\n"), tt.diagnostic) {
				t.Fatalf("source %q: want %q, got %v", tt.source, tt.diagnostic, p.Errors())
			}
		})
	}
}

func TestDeclarationContractPreservesSingleSiteBinders(t *testing.T) {
	for _, source := range []string{"Box[T]: type = | Wrap: T", "Box: type[T] = | Wrap: T"} {
		p := New(scanner.New(source))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 || len(tree.Statements) != 1 {
			t.Fatalf("%s: %v", source, p.Errors())
		}
		decl, ok := tree.Statements[0].(*ast.ADTType)
		if !ok || len(decl.TypeParams) != 1 || decl.TypeParams[0].Name.Value != "T" {
			t.Fatalf("%s: binder lost in %#v", source, tree.Statements[0])
		}
	}
	p := New(scanner.New("id[T]: (x: T): T = x"))
	tree := p.ParseProgram()
	if len(p.Errors()) != 0 || len(tree.Statements) != 1 {
		t.Fatal(p.Errors())
	}
	fn, ok := tree.Statements[0].(*ast.FunctionStatement)
	if !ok || len(fn.TypeParams) != 1 || fn.TypeParams[0].Name.Value != "T" {
		t.Fatal("generic function binder lost")
	}
}

func TestDeclarationContractPreservesInterfaceSyntax(t *testing.T) {
	for _, source := range []string{
		"I[T]: interface = fn (self) m(x: T) -> T",
		"I: interface = fn (self: i32) m(x: i32) -> i32",
		"I: interface = fn (self) m(xs: ...i32) -> i32",
	} {
		p := New(scanner.New(source))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 || len(tree.Statements) != 1 {
			t.Fatalf("%s: %v", source, p.Errors())
		}
		decl, ok := tree.Statements[0].(*ast.InterfaceType)
		if !ok {
			t.Fatalf("want interface, got %T", tree.Statements[0])
		}
		printed := decl.String()
		q := New(scanner.New(printed))
		round := q.ParseProgram()
		if len(q.Errors()) != 0 || len(round.Statements) != 1 || round.Statements[0].String() != printed {
			t.Fatalf("lost syntax for %s: %v", source, q.Errors())
		}
		if printed != source {
			t.Fatalf("contract changed: %s -> %s", source, printed)
		}
	}
}
