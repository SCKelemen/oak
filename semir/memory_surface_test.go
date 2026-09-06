package semir

import "testing"

func TestEveryAtomicSurfaceBuiltinHasLegalOrder(t *testing.T) {
	names := []string{
		"atomic_load_relaxed", "atomic_load_acquire", "atomic_load_seq_cst",
		"atomic_store_relaxed", "atomic_store_release", "atomic_store_seq_cst",
		"atomic_fetch_add_relaxed", "atomic_fetch_add_acquire", "atomic_fetch_add_release",
		"atomic_fetch_add_acq_rel", "atomic_fetch_add_seq_cst",
		"atomic_fence_acquire", "atomic_fence_release", "atomic_fence_acq_rel", "atomic_fence_seq_cst",
	}
	for _, name := range names {
		spec, ok := LookupAtomicBuiltin(name)
		if !ok {
			t.Fatalf("surface builtin %s not found", name)
		}
		if spec.Name != name {
			t.Fatalf("lookup changed builtin identity: got %q want %q", spec.Name, name)
		}
		if !LegalAtomicOrder(spec.Operation, spec.Order) {
			t.Fatalf("surface builtin %s exposes illegal %s/%s", name, spec.Operation, spec.Order)
		}
		if _, err := spec.Effect(); err != nil {
			t.Fatalf("surface builtin %s has invalid semantic effect: %v", name, err)
		}
	}
}

func TestAtomicSurfaceDoesNotExposeIllegalOrderPairs(t *testing.T) {
	for _, name := range []string{
		"atomic_load_release", "atomic_load_acq_rel",
		"atomic_store_acquire", "atomic_store_acq_rel",
		"atomic_fence_relaxed",
	} {
		if _, ok := LookupAtomicBuiltin(name); ok {
			t.Fatalf("illegal operation/order pair unexpectedly exposed as %s", name)
		}
	}
}

func TestAtomicBuiltinLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		spec, ok := LookupAtomicBuiltin("atomic_fetch_add_acq_rel")
		if !ok || spec.Kind != AtomicBuiltinFetchAdd {
			panic("lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("atomic builtin lookup allocated %.2f objects per call; want zero", allocs)
	}
}
