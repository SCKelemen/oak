package evaluator

import (
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestAtomicEvaluatorCellIdentityAndRMW(t *testing.T) {
	input := `
package main
counter: Atomic[u64]
atomic_store_release(counter, u64(41))
old: u64 = atomic_fetch_add_acq_rel(counter, u64(1))
assert(old == u64(41))
atomic_fence_acquire()
atomic_load_acquire(counter)
`
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := Eval(program, object.NewEnvironment())
	integer, ok := result.(*object.Integer)
	if !ok {
		t.Fatalf("result is %T (%v), want integer 42", result, result)
	}
	if integer.Value != 42 {
		t.Fatalf("atomic evaluator result = %d, want 42", integer.Value)
	}
}

func TestAtomicEvaluatorRejectsDirectAssignment(t *testing.T) {
	input := `
package main
counter: Atomic[u64]
counter = u64(3)
`
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	result := Eval(program, object.NewEnvironment())
	if _, ok := result.(*object.Error); !ok {
		t.Fatalf("direct atomic assignment produced %T, want evaluator error", result)
	}
}
