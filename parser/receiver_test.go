package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParser_FunctionReceiverPreservesIdentifierAndType(t *testing.T) {
	input := "fn (uart: Uart) read() -> i32 = 0"

	p := New(scanner.New(input))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}
	if len(program.Statements) != 1 {
		t.Fatalf("expected 1 statement, got %d", len(program.Statements))
	}
	method, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("expected receiver function, got %T", program.Statements[0])
	}
	if method.Receiver == nil || method.Receiver.Name == nil || method.Receiver.Name.Value != "uart" {
		t.Fatalf("receiver identifier was not preserved: %#v", method.Receiver)
	}
	if method.Receiver.Type == nil || method.Receiver.Type.String() != "Uart" {
		t.Fatalf("receiver type was not preserved: %#v", method.Receiver.Type)
	}
	if method.Name == nil || method.Name.Value != "read" {
		t.Fatalf("method name was not preserved: %#v", method.Name)
	}
}
