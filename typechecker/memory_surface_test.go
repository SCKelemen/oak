package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func checkAtomicSource(t *testing.T, source string) []string {
	t.Helper()
	p := parser.New(scanner.New(source))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	return tc.Errors()
}

func requireAtomicErrorContains(t *testing.T, errs []string, fragment string) {
	t.Helper()
	for _, err := range errs {
		if strings.Contains(err, fragment) {
			return
		}
	}
	t.Fatalf("errors %v do not contain %q", errs, fragment)
}

func TestAtomicSurfaceTypesEndToEnd(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
counter: Atomic[u64]
fn bump() -> u64
  atomic_store_release(counter, u64(40))
  before: u64 = atomic_fetch_add_acq_rel(counter, u64(2))
  assert(before == u64(40))
  atomic_fence_seq_cst()
  atomic_load_acquire(counter)
`)
	if len(errs) != 0 {
		t.Fatalf("valid atomic program rejected: %v", errs)
	}
}

func TestAtomicSurfaceRejectsUnsupportedCarrier(t *testing.T) {
	errs := checkAtomicSource(t, "package main\ncounter: Atomic[int]\n")
	requireAtomicErrorContains(t, errs, "fixed-width integer carrier")
}

func TestAtomicSurfaceRejectsInitializerAndCellCopy(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
first: Atomic[u64] = u64(1)
second: Atomic[u64]
second = first
`)
	requireAtomicErrorContains(t, errs, "zero-initialized")
	requireAtomicErrorContains(t, errs, "not assignable")
}

func TestAtomicSurfaceRejectsByValueFunctionTransport(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
fn bad(cell: Atomic[u64]) -> u64
  atomic_load_relaxed(cell)
`)
	requireAtomicErrorContains(t, errs, "cannot be passed by value")
}

func TestAtomicSurfaceRejectsNonCellOperandAndWrongValue(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
counter: Atomic[u64]
fn bad() -> u64
  atomic_store_release(counter, "bad")
  atomic_load_relaxed(u64(1))
`)
	requireAtomicErrorContains(t, errs, "value must be u64")
	requireAtomicErrorContains(t, errs, "requires a named Atomic[T] cell")
}
