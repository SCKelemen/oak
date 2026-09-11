package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// The defer rewrite (docs/spec/10-syntax.md section 4b): deferred
// statements move to the end of their block in reverse order, after the
// block's value is bound to a temporary; they are cloned in before every
// break the block's later statements reach; defer outside a block is an
// error.
func parseDeferProgram(t *testing.T, src string) *ast.Program {
	t.Helper()
	p := New(scanner.New(src))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	return program
}

func TestDeferRewriteOrderAndTail(t *testing.T) {
	program := parseDeferProgram(t, `
f: (): u32 {
  defer a()
  defer b()
  c()
}
`)
	fn := program.Statements[0].(*ast.FunctionStatement)
	block := fn.Body.(*ast.BlockExpression).Block
	got := make([]string, 0, len(block.Statements))
	for _, stmt := range block.Statements {
		got = append(got, stmt.String())
	}
	joined := strings.Join(got, " ; ")
	if joined != "c() ; b() ; a()" {
		t.Fatalf("deferred statements must follow the tail in reverse order, got %s", joined)
	}
	if block.DeferredFrom != 1 {
		t.Fatalf("DeferredFrom must mark where the deferred statements start, got %d", block.DeferredFrom)
	}
	for _, stmt := range block.Statements {
		if _, isDefer := stmt.(*ast.DeferStatement); isDefer {
			t.Fatalf("no DeferStatement may survive parsing: %s", joined)
		}
	}
}

func TestDeferRewriteBeforeBreak(t *testing.T) {
	program := parseDeferProgram(t, `
f: (): u32 {
  while true {
    defer step()
    done ? { break } | { }
    work()
  }
  0
}
`)
	fn := program.Statements[0].(*ast.FunctionStatement)
	body := fn.Body.(*ast.BlockExpression).Block
	loop := body.Statements[0].(*ast.WhileStatement)
	text := loop.Body.String()
	if strings.Count(text, "step()") != 2 {
		t.Fatalf("step() must run before the break and at the end of the body: %s", text)
	}
	arm := loop.Body.Statements[0].(*ast.ExpressionStatement).Expression.(*ast.MatchExpression).Arms[0].Body.(*ast.BlockExpression).Block
	if len(arm.Statements) != 2 || arm.Statements[0].String() != "step()" {
		t.Fatalf("the deferred statement must precede the break: %s", arm.String())
	}
	if _, isBreak := arm.Statements[1].(*ast.BreakStatement); !isBreak {
		t.Fatalf("break must remain last in its arm: %s", arm.String())
	}
}

func TestDeferOutsideBlockRejected(t *testing.T) {
	p := New(scanner.New("defer close(h)\n"))
	p.ParseProgram()
	if len(p.Errors()) == 0 || !strings.Contains(strings.Join(p.Errors(), " "), "inside a block") {
		t.Fatalf("defer outside a block must be rejected, got %v", p.Errors())
	}
}
