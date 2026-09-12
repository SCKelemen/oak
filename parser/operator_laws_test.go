package parser

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/scanner"
)

// The `laws { ... }` clause on an operator definition (docs/spec/10-syntax.md
// section 14a) parses after the effect clauses, at most once, and prints back.
func TestOperatorLawsClause(t *testing.T) {
	src := "operator(+) add: (a: Vec, b: Vec): Vec effects { } laws { associative, commutative, identity(zero()), idempotent } = a\n"
	program := parseLaws(t, src)
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok || fn.Operator != "+" {
		t.Fatalf("statement = %T %v", program.Statements[0], program.Statements[0])
	}
	if len(fn.Laws) != 4 || fn.Laws[0].Name != "associative" || fn.Laws[1].Name != "commutative" || fn.Laws[2].Name != "identity" || fn.Laws[3].Name != "idempotent" {
		t.Fatalf("laws = %v", fn.Laws)
	}
	if fn.Laws[2].Argument == nil || fn.Laws[2].Argument.String() != "zero()" || fn.Laws[0].Argument != nil {
		t.Fatalf("identity carries its element and the others none: %v", fn.Laws)
	}
	if !fn.EffectsDeclared {
		t.Fatal("the effects clause before laws must still be recorded")
	}
	if printed := fn.String(); !strings.Contains(printed, "laws { associative, commutative, identity(zero()), idempotent }") {
		t.Fatalf("laws must print back: %s", printed)
	}
	// A plain function accepts the clause syntactically; the checker rejects it.
	plain := parseLaws(t, "f: (a: u32, b: u32): u32 laws { associative } = a\n")
	if fn := plain.Statements[0].(*ast.FunctionStatement); len(fn.Laws) != 1 {
		t.Fatalf("laws = %v", fn.Laws)
	}
	// Two clauses, an empty clause, and a non-identifier law are syntax errors.
	for _, bad := range []string{
		"operator(+) add: (a: Vec, b: Vec): Vec laws { associative } laws { commutative } = a\n",
		"operator(+) add: (a: Vec, b: Vec): Vec laws { } = a\n",
		"operator(+) add: (a: Vec, b: Vec): Vec laws { 1 } = a\n",
	} {
		p := New(scanner.New(bad))
		p.ParseProgram()
		if len(p.Errors()) == 0 {
			t.Fatalf("must be rejected: %s", bad)
		}
	}
}

func parseLaws(t *testing.T, src string) *ast.Program {
	t.Helper()
	p := New(scanner.New(src))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("parse errors: %v", p.Errors())
	}
	if len(program.Statements) != 1 {
		t.Fatalf("statements = %d", len(program.Statements))
	}
	return program
}
