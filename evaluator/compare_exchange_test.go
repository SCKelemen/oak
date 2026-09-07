package evaluator

import (
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func evalCompareExchangeProgram(t *testing.T, input string) object.Object {
	t.Helper()
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	return Eval(program, object.NewEnvironment())
}

func TestCompareExchangeEvaluatorReturnsExpectedOnSuccess(t *testing.T) {
	result := evalCompareExchangeProgram(t, `
package main
counter: Atomic[u64]
atomic_store_relaxed(counter, u64(7))
observed: u64 = atomic_compare_exchange_acq_rel_acquire(counter, u64(7), u64(9))
assert(observed == u64(7))
atomic_load_relaxed(counter)
`)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 9 {
		t.Fatalf("successful CAS result = %T %v, want final integer 9", result, result)
	}
}

func TestCompareExchangeEvaluatorReturnsObservedOnFailure(t *testing.T) {
	result := evalCompareExchangeProgram(t, `
package main
counter: Atomic[u64]
atomic_store_relaxed(counter, u64(11))
observed: u64 = atomic_compare_exchange_relaxed_relaxed(counter, u64(7), u64(9))
assert(observed == u64(11))
atomic_load_relaxed(counter)
`)
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 11 {
		t.Fatalf("failed CAS result = %T %v, want unchanged integer 11", result, result)
	}
}
