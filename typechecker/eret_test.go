package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestEretIsNullaryAndReturnsNever(t *testing.T) {
	p := parser.New(scanner.New(`
package main
fn enter() -> never
  arm64.eret()
`))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("valid ERET function rejected: %v", errs)
	}
	fn, ok := tc.Env().GetType("enter")
	if !ok {
		t.Fatal("enter missing from type environment")
	}
	ft, ok := fn.(*FunctionType)
	if !ok {
		t.Fatalf("enter has non-function type %T", fn)
	}
	if _, ok := ft.ReturnType.(*NeverType); !ok {
		t.Fatalf("ERET function return type = %T, want NeverType", ft.ReturnType)
	}
}

func TestEretRejectsOperands(t *testing.T) {
	p := parser.New(scanner.New(`
package main
fn bad(x: u64) -> never
  arm64.eret(x)
`))
	program := p.ParseProgram()
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	if len(tc.Errors()) == 0 {
		t.Fatal("ERET with an operand must be rejected")
	}
}

// eret_x0 carries one u64 and is still never-typed; the plain form stays
// nullary and the carrying form refuses a second value.
func TestEretX0CarriesOneU64(t *testing.T) {
	p := parser.New(scanner.New(`
package main
fn enter(arg: u64) -> never
  arm64.eret_x0(arg)
`))
	program := p.ParseProgram()
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	if len(tc.Errors()) != 0 {
		t.Fatalf("eret_x0 with one u64 must typecheck: %v", tc.Errors())
	}
	ft, ok := arm64Intrinsics["eret_x0"]
	if !ok || len(ft.Parameters) != 1 {
		t.Fatalf("eret_x0 signature: %#v", ft)
	}
	if _, isNever := ft.ReturnType.(*NeverType); !isNever {
		t.Fatalf("eret_x0 return type = %T, want NeverType", ft.ReturnType)
	}
	p = parser.New(scanner.New(`
package main
fn bad(a: u64, b: u64) -> never
  arm64.eret_x0(a, b)
`))
	program = p.ParseProgram()
	tc = New(object.NewEnvironment())
	tc.CheckProgram(program)
	if len(tc.Errors()) == 0 {
		t.Fatal("eret_x0 with two operands must be rejected")
	}
}
