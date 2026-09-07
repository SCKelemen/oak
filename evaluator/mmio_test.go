package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestMmioEvaluatorFailsClosed(t *testing.T) {
	input := `
package main
arm64.mmio_read_rw_u32(arm64.mmio_unsafe_rw_u32(u64(4096)))
`
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := Eval(program, object.NewEnvironment())
	err, ok := result.(*object.Error)
	if !ok {
		t.Fatalf("MMIO evaluation produced %T, want error", result)
	}
	if !strings.Contains(err.Message, "requires the native AArch64 backend") {
		t.Fatalf("MMIO evaluator failure is not explicit: %s", err.Message)
	}
}
