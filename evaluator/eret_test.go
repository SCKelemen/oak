package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestEretEvaluatorFailsClosed(t *testing.T) {
	p := parser.New(scanner.New(`
package main
fn enter() -> never
  arm64.eret()
`))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := Eval(program, object.NewEnvironment())
	if result == nil {
		t.Fatal("host evaluator must not pretend ERET executed")
	}
	if !strings.Contains(result.Inspect(), "non-returning control-transfer") {
		t.Fatalf("unexpected ERET evaluator result: %s", result.Inspect())
	}
}
