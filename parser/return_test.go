package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func parseFunctionBody(t *testing.T, src string) (*ast.BlockStatement, []string) {
	t.Helper()
	p := New(scanner.New(src))
	program := p.ParseProgram()
	if program == nil || len(program.Statements) == 0 {
		return nil, p.Errors()
	}
	var body *ast.BlockStatement
	switch s := program.Statements[0].(type) {
	case *ast.FunctionStatement:
		if block, ok := s.Body.(*ast.BlockExpression); ok {
			body = block.Block
		}
	case *ast.VariableDeclaration:
		if lit, ok := s.Value.(*ast.FunctionLiteral); ok {
			body = lit.Body
		}
	}
	return body, p.Errors()
}

func hasReturn(t *testing.T, body *ast.BlockStatement) bool {
	t.Helper()
	return blockReturns(body, true)
}

// A guard clause nests the rest of the body into the other arm; the
// conditional becomes the body's value and no flag is declared.
func TestReturnLowersGuardClauseToNesting(t *testing.T) {
	body, errs := parseFunctionBody(t, "f: (x: u32): u32 {\n  x == u32(0) ? { return u32(7) }\n  y: u32 = x + u32(1)\n  y * u32(2)\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if hasReturn(t, body) {
		t.Fatalf("returns must be lowered:\n%s", body.String())
	}
	text := body.String()
	if strings.Contains(text, "return__") {
		t.Fatalf("a guard clause needs no flag:\n%s", text)
	}
	if len(body.Statements) != 1 {
		t.Fatalf("the conditional is the body's one statement:\n%s", text)
	}
	if !strings.Contains(text, "y * 2") && !strings.Contains(text, "(y * u32(2))") && !strings.Contains(text, "y * u32(2)") {
		t.Fatalf("the rest of the body is nested into the falling arm:\n%s", text)
	}
}

// A return inside a loop becomes the cell and flag, a break, and the
// propagated return after the loop, nested at the function level.
func TestReturnLowersLoopReturnToFlagAndBreak(t *testing.T) {
	body, errs := parseFunctionBody(t, "f: (n: u32): u32 {\n  i: u32 = u32(0)\n  while i < n {\n    i == u32(3) ? { return i }\n    i = i + u32(1)\n  }\n  u32(64)\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	if hasReturn(t, body) {
		t.Fatalf("returns must be lowered:\n%s", body.String())
	}
	text := body.String()
	for _, want := range []string{"return__value", "return__done", "break"} {
		if !strings.Contains(text, want) {
			t.Fatalf("the loop form carries %s:\n%s", want, text)
		}
	}
	decl, isDecl := body.Statements[0].(*ast.VariableDeclaration)
	if !isDecl || decl.Name.Value != "return__value" || decl.Value == nil {
		t.Fatalf("the cell is declared first, initialized:\n%s", text)
	}
}

// Diagnostics: a value in a unit function, none in a valued one, a value
// from inside a loop of an unannotated literal, and a return outside a
// function body.
func TestReturnDiagnostics(t *testing.T) {
	cases := map[string]string{
		"g: (): () {\n  return u32(1)\n}\n":                                  "a unit function returns no value",
		"h: (): u32 {\n  return\n}\n":                                        "return needs the function's value",
		"k: () = fn(n: u32) {\n  while n > u32(0) {\n    return n\n  }\n}\n": "return type annotated",
	}
	for src, want := range cases {
		_, errs := parseFunctionBody(t, src)
		joined := strings.Join(errs, "\n")
		if !strings.Contains(joined, want) {
			t.Errorf("%q: want a diagnostic containing %q, got:\n%s", src, want, joined)
		}
	}
}
