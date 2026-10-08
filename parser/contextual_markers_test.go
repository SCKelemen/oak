package parser

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
	"testing"
)

func TestContextualMarkerNamesRemainCallable(t *testing.T) {
	for _, src := range []string{"operator(1)", "operator(-1)", "operator(x)", "export(\"thing\")", "export(name)", "export(\"thing\")\nx: u32 = 1", "export(\"thing\")\nfn f(): u32 = 1", "operator(1); x: u32 = 2"} {
		p := New(scanner.New(src))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatalf("%s: %v", src, p.Errors())
		}
		stmt, ok := tree.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			t.Fatalf("%s: want call statement, got %T", src, tree.Statements[0])
		}
		if _, ok := stmt.Expression.(*ast.InvocationExpression); !ok {
			t.Fatalf("%s: want invocation, got %T", src, stmt.Expression)
		}
	}
}

func TestContextualMarkersStillDeclareFunctions(t *testing.T) {
	for _, src := range []string{"operator(+) add: (x, y: u32): u32 = x + y", "export(\"inc\")\npub inc: (x: u32): u32 = x + 1", "export(\"inc\") pub inc: (x: u32): u32 = x + 1"} {
		p := New(scanner.New(src))
		tree := p.ParseProgram()
		if len(p.Errors()) != 0 {
			t.Fatalf("%s: %v", src, p.Errors())
		}
		fn, ok := tree.Statements[0].(*ast.FunctionStatement)
		if !ok || (fn.Operator == "" && fn.ExportSymbol == "") {
			t.Fatalf("lost marker for %s: %#v", src, tree.Statements[0])
		}
	}
}
