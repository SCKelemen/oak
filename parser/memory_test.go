package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestAtomicTypeAndBuiltinSyntaxParse(t *testing.T) {
	input := `
package main

counter: Atomic[u64]

fn bump() -> u64
  atomic_fetch_add_relaxed(counter, u64(1))
`
	p := New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	if len(program.Statements) < 3 {
		t.Fatalf("expected package, cell, and function statements; got %d", len(program.Statements))
	}
	decl, ok := program.Statements[1].(*ast.VariableDeclaration)
	if !ok {
		t.Fatalf("statement 1 is %T, want variable declaration", program.Statements[1])
	}
	atomicType, ok := decl.Type.(*ast.IndexExpression)
	if !ok {
		t.Fatalf("Atomic[u64] parsed as %T, want IndexExpression", decl.Type)
	}
	base, ok := atomicType.Left.(*ast.Identifier)
	if !ok || base.Value != "Atomic" {
		t.Fatalf("atomic type base = %#v, want Atomic", atomicType.Left)
	}
	carrier, ok := atomicType.Index.(*ast.Identifier)
	if !ok || carrier.Value != "u64" {
		t.Fatalf("atomic carrier = %#v, want u64", atomicType.Index)
	}

	fn, ok := program.Statements[2].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("statement 2 is %T, want function", program.Statements[2])
	}
	call, ok := fn.Body.(*ast.InvocationExpression)
	if !ok {
		t.Fatalf("single-expression bump body is %T, want invocation", fn.Body)
	}
	callee, ok := call.Function.(*ast.Identifier)
	if !ok || callee.Value != "atomic_fetch_add_relaxed" {
		t.Fatalf("callee = %#v, want atomic_fetch_add_relaxed", call.Function)
	}
}
