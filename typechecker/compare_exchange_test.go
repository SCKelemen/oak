package typechecker

import "testing"

func TestCompareExchangeTypesAndReturnsObservedCarrier(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
counter: Atomic[u64]
fn cas(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_acq_rel_acquire(counter, expected, desired)
`)
	if len(errs) != 0 {
		t.Fatalf("valid compare-exchange rejected: %v", errs)
	}
}

func TestCompareExchangeRejectsWrongExpectedAndDesiredTypes(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
counter: Atomic[u64]
fn bad() -> u64 {
  atomic_compare_exchange_acq_rel_acquire(counter, "wrong", u64(2))
  atomic_compare_exchange_acq_rel_acquire(counter, u64(1), "wrong")
}
`)
	requireAtomicErrorContains(t, errs, "expected value must be u64")
	requireAtomicErrorContains(t, errs, "desired value must be u64")
}

func TestCompareExchangeRejectsTemporaryCell(t *testing.T) {
	errs := checkAtomicSource(t, `
package main
counter: Atomic[u64]
fn bad() -> u64
  atomic_compare_exchange_relaxed_relaxed(atomic_load_relaxed(counter), u64(0), u64(1))
`)
	requireAtomicErrorContains(t, errs, "requires a named Atomic[T] cell")
}
