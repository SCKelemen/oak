package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func parseProgramForBlockTest(t *testing.T, input string) *ast.Program {
	t.Helper()
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) > 0 {
		t.Fatalf("parser errors for %q: %v", input, errs)
	}
	return program
}

// Function block bodies must retain every statement, not only the trailing
// expression — the checkers and backends see the whole body.
func TestFunctionBlockBodyRetainsAllStatements(t *testing.T) {
	program := parseProgramForBlockTest(t, "fn f() -> i32 { x: i32 = 1\nx }")
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("expected FunctionStatement, got %T", program.Statements[0])
	}
	body, ok := fn.Body.(*ast.BlockExpression)
	if !ok {
		t.Fatalf("expected BlockExpression body, got %T", fn.Body)
	}
	if got := len(body.Block.Statements); got != 2 {
		t.Fatalf("block body retained %d statements, want 2: %s", got, body.Block.String())
	}
	result := body.Result()
	ident, ok := result.(*ast.Identifier)
	if !ok || ident.Value != "x" {
		t.Fatalf("block result = %#v, want identifier x", result)
	}
}

// IDENT '[' in statement position is an index/slice expression statement
// unless the bracket group is followed by ':' (a generic type definition).
func TestIndexAndSliceExpressionStatementsParse(t *testing.T) {
	inputs := []string{
		"fn f(buf: [16]u8) -> u8 { v: []u8 = buf[0:8]\nbuf[0] }",
		"fn f(buf: [16]u8) -> []u8 { buf[0:8] }",
		"fn f(m: [4]u8) -> u8 { m[0]\nm[1] }",
	}
	for _, input := range inputs {
		parseProgramForBlockTest(t, input)
	}
}

// Generic type definitions keep their routing: Name[E]: type = ...
func TestGenericTypeDefinitionStillParses(t *testing.T) {
	program := parseProgramForBlockTest(t, "Option[T]: type = Some(T) | None")
	if _, ok := program.Statements[0].(*ast.ADTType); !ok {
		t.Fatalf("expected ADTType, got %T", program.Statements[0])
	}
}

// Variadic markers parse on the last parameter only; two dots are illegal.
func TestVariadicParameterParsing(t *testing.T) {
	program := parseProgramForBlockTest(t, "fn total(base: i32, rest: ...i32) -> i32 { base }")
	fn := program.Statements[0].(*ast.FunctionStatement)
	if len(fn.Parameters) != 2 || fn.Parameters[0].Variadic || !fn.Parameters[1].Variadic {
		t.Fatalf("variadic flags wrong: %#v", fn.Parameters)
	}
	if fn.Parameters[1].Type.String() != "i32" {
		t.Fatalf("variadic element type = %s, want i32", fn.Parameters[1].Type.String())
	}

	p := New(scanner.New("fn bad(rest: ...i32, tail: i32) -> i32 { tail }"))
	p.ParseProgram()
	if len(p.Errors()) == 0 {
		t.Fatal("non-last variadic parameter must be rejected")
	}

	p = New(scanner.New("x: i32 = 1 .. 2"))
	p.ParseProgram()
	if len(p.Errors()) == 0 {
		t.Fatal("two-dot token must be illegal")
	}
}
