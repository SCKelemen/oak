package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// `forall (x: T) { ... }` and `exists (x: T) { ... }` parse as quantifier
// expressions only in the binder form; elsewhere the words are
// identifiers (docs/spec/10-syntax.md section 3e).
func TestParseQuantifierExpression(t *testing.T) {
	p := New(scanner.New("f: (): Bool = forall (x: u8, y: u8) { x + y == y + x }"))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("statement is %T", program.Statements[0])
	}
	q, ok := fn.Body.(*ast.QuantifierExpression)
	if !ok {
		t.Fatalf("body is %T: %s", fn.Body, fn.Body.String())
	}
	if !q.Universal || len(q.Binders) != 2 || q.Binders[1].Name.Value != "y" || q.Body == nil {
		t.Fatalf("quantifier parsed as %s", q.String())
	}
	if got := q.String(); got != "forall (x: u8, y: u8) { ((x + y) == (y + x)) }" {
		t.Errorf("String() = %q", got)
	}

	p = New(scanner.New("g: (): u8 {\n  exists: u8 = u8(1)\n  exists\n}"))
	program = p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	fn = program.Statements[0].(*ast.FunctionStatement)
	if _, isQuantifier := fn.Body.(*ast.QuantifierExpression); isQuantifier {
		t.Fatalf("a local named exists parsed as a quantifier")
	}
}
