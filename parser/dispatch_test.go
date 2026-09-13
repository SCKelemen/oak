package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// The dispatch clause (docs/spec/10-syntax.md section 14b) follows the
// effect and laws clauses and prints back as declared.
func TestDispatchClauseParses(t *testing.T) {
	p := New(scanner.New(`
count: (xs: []u8) -> u32 effects { } dispatch { sve: count_sve, rvv: count_rvv } = u32(len(xs))
`))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok || len(fn.Dispatch) != 2 {
		t.Fatalf("expected a function with two dispatch slots, got %T %+v", program.Statements[0], fn)
	}
	if fn.Dispatch[0].Feature != "sve" || fn.Dispatch[0].Realization != "count_sve" || fn.Dispatch[1].Feature != "rvv" || fn.Dispatch[1].Realization != "count_rvv" {
		t.Fatalf("slots: %+v %+v", fn.Dispatch[0], fn.Dispatch[1])
	}
	if !strings.Contains(fn.String(), "dispatch { sve: count_sve, rvv: count_rvv }") {
		t.Fatalf("printer: %s", fn.String())
	}
	for _, bad := range []string{
		"count: (xs: []u8) -> u32 dispatch { } = u32(len(xs))\n",
		"count: (xs: []u8) -> u32 dispatch { sve count_sve } = u32(len(xs))\n",
		"count: (xs: []u8) -> u32 dispatch { sve: a } dispatch { rvv: b } = u32(len(xs))\n",
	} {
		p := New(scanner.New(bad))
		p.ParseProgram()
		if len(p.Errors()) == 0 {
			t.Errorf("expected a parse error for %q", bad)
		}
	}
}
