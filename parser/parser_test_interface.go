package parser

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

func TestParser_InterfaceType(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		wantName string
		wantErr  bool
	}{
		{
			name:     "simple interface with one method",
			input:    "Reader: interface = fn (self) read(buf: [*]Byte) -> Result[u32, Error]",
			wantName: "Reader",
			wantErr:  false,
		},
		{
			name:     "interface with receiver type",
			input:    "IntrusiveListNode[T, Tag]: interface = fn (self: *T) hook(_: Tag) -> *ListHook[T, Tag]",
			wantName: "IntrusiveListNode",
			wantErr:  false,
		},
		{
			name:     "interface with type parameters",
			input:    "Writer[T]: interface = fn (self) write(data: T) -> Result[u32, Error]",
			wantName: "Writer",
			wantErr:  false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			lxr := scanner.New(tt.input)
			p := New(lxr)
			program := p.ParseProgram()

			if tt.wantErr {
				if len(p.Errors()) == 0 {
					t.Errorf("expected errors but got none")
				}
				return
			}

			if len(p.Errors()) > 0 {
				t.Errorf("unexpected errors: %v", p.Errors())
				return
			}

			if len(program.Statements) != 1 {
				t.Fatalf("expected 1 statement, got %d", len(program.Statements))
			}

			iface, ok := program.Statements[0].(*ast.InterfaceType)
			if !ok {
				t.Fatalf("expected *ast.InterfaceType, got %T", program.Statements[0])
			}

			if iface.Name.Value != tt.wantName {
				t.Errorf("expected interface name %q, got %q", tt.wantName, iface.Name.Value)
			}

			if len(iface.Methods) == 0 {
				t.Error("expected at least one method, got 0")
			}

			// Check that method has name, parameters, and return type
			method := iface.Methods[0]
			if method.Name == nil {
				t.Error("method name is nil")
			}
			if method.ReturnType == nil {
				t.Error("method return type is nil")
			}
		})
	}
}

func TestParser_InterfaceMethod_Parameters(t *testing.T) {
	input := "Reader: interface = fn (self) read(buf: [*]Byte, len: u32) -> Result[u32, Error]"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}

	iface := program.Statements[0].(*ast.InterfaceType)
	method := iface.Methods[0]

	if len(method.Parameters) != 2 {
		t.Errorf("expected 2 parameters, got %d", len(method.Parameters))
	}

	if method.Parameters[0].Name.Value != "buf" {
		t.Errorf("expected first parameter name 'buf', got %q", method.Parameters[0].Name.Value)
	}

	if method.Parameters[1].Name.Value != "len" {
		t.Errorf("expected second parameter name 'len', got %q", method.Parameters[1].Name.Value)
	}
}

func TestParser_InterfaceMethod_ReceiverType(t *testing.T) {
	input := "IntrusiveListNode[T, Tag]: interface = fn (self: *T) hook(_: Tag) -> *ListHook[T, Tag]"

	lxr := scanner.New(input)
	p := New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		t.Fatalf("unexpected errors: %v", p.Errors())
	}

	iface := program.Statements[0].(*ast.InterfaceType)
	method := iface.Methods[0]

	if method.ReceiverType == nil {
		t.Error("expected receiver type, got nil")
	}
}

