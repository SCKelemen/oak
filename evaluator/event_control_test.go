package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestEventControlEvaluatorFailsClosed(t *testing.T) {
	p := parser.New(scanner.New(`arm64.wfi()`))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := Eval(program, object.NewEnvironment())
	if result == nil || !strings.Contains(result.Inspect(), "requires the native AArch64 backend") {
		t.Fatalf("expected fail-closed event-control error, got %v", result)
	}
}
