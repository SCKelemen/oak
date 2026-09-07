package evaluator

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestSystemRegisterEvaluatorFailsClosed(t *testing.T) {
	for _, input := range []string{
		"package main\narm64.read_hcr_el2()\n",
		"package main\narm64.write_hcr_el2(u64(1))\n",
	} {
		p := parser.New(scanner.New(input))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			t.Fatalf("parser errors: %v", errs)
		}
		result := Eval(program, object.NewEnvironment())
		err, ok := result.(*object.Error)
		if !ok {
			t.Fatalf("system-register evaluation produced %T, want error", result)
		}
		if !strings.Contains(err.Message, "requires the native AArch64 backend") {
			t.Fatalf("system-register evaluator failure is not explicit: %s", err.Message)
		}
	}
}
