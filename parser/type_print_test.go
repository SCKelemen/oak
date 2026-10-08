package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"testing"
)

func TestTypeSyntaxPrinting(t *testing.T) {
	for _, typ := range []string{"[]u32", "[*]u8", "[align 16]u32", "[* align 64]f32", "[4]u8", "[N]u8", "[N + 1]u8", "Tensor[R]", "Pair[u8, []u32]", "pkg.Pair[u8, Pair[u16, u32]]", "[2]Pair[u8, u16]"} {
		t.Run(typ, func(t *testing.T) {
			source := "f[N]: (x: " + typ + "): () (kernel) = {}"
			p := New(scanner.New(source))
			tree := p.ParseProgram()
			if len(p.Errors()) != 0 {
				t.Fatalf("parse: %v", p.Errors())
			}
			fn := tree.Statements[0].(*ast.FunctionStatement)
			printed := fn.Parameters[0].Type.String()
			if printed != typ {
				t.Fatalf("type prints as %q, want %q", printed, typ)
			}
			q := New(scanner.New(fn.String()))
			round := q.ParseProgram()
			if len(q.Errors()) != 0 {
				t.Fatalf("reparse: %v", q.Errors())
			}
			if got := round.Statements[0].(*ast.FunctionStatement).Parameters[0].Type.String(); got != typ {
				t.Fatalf("reparsed type %q, want %q", got, typ)
			}
		})
	}
}

func TestValueIndexPrintingDistinguishesMember(t *testing.T) {
	for source, want := range map[string]string{"a[i]": "(a[i])", "a.field": "(a.field)", "a[4]": "(a[4])"} {
		p := New(scanner.New(source))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatal(p.Errors())
		}
		if got := tree.Statements[0].String(); got != want {
			t.Fatalf("%s prints %s, want %s", source, got, want)
		}
	}
}

func TestNestedFunctionTypeRowsKeepTheirTarget(t *testing.T) {
	for _, returned := range []string{"(u32) -> u32", "[](u32) -> u32", "[*](u32) -> u32"} {
		source := "f: (x: (u32) -> (" + returned + ") effects { Host.Read }): () (kernel) = {}"
		p := New(scanner.New(source))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatal(p.Errors())
		}
		original := tree.Statements[0].(*ast.FunctionStatement)
		q := New(scanner.New(original.String()))
		round := q.ParseProgram()
		if len(q.Errors()) != 0 {
			t.Fatal(q.Errors())
		}
		got := round.Statements[0].(*ast.FunctionStatement).Parameters[0].Type.(*ast.FunctionTypeExpression)
		tail := got.Return
		if array, ok := tail.(*ast.IndexExpression); ok {
			tail = array.Left
		}
		if !got.EffectsDeclared || tail.(*ast.FunctionTypeExpression).EffectsDeclared {
			t.Fatalf("effect row attached to returned callable: %s", original.String())
		}
	}
}

func TestCompoundArrayLengthPrinting(t *testing.T) {
	for _, typ := range []string{"[N * 2 + 1]u32", "[N + 1 + 2]u32", "[(N + 1) * 2]u32", "[N * (M + 1)]u32"} {
		p := New(scanner.New("f[N,M]: (x: " + typ + "): () (kernel) = {}"))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatal(p.Errors())
		}
		fn := tree.Statements[0].(*ast.FunctionStatement)
		q := New(scanner.New(fn.String()))
		round := q.ParseProgram()
		if len(q.Errors()) != 0 {
			t.Fatalf("%s: %v", fn.String(), q.Errors())
		}
		if round.Statements[0].String() != fn.String() {
			t.Fatalf("changed grouping: %s -> %s", fn.String(), round.Statements[0].String())
		}
	}
}
