package semir

import "testing"

func TestCompareExchangeOrderRelation(t *testing.T) {
	legal := [][2]MemoryOrder{
		{MemoryOrderRelaxed, MemoryOrderRelaxed},
		{MemoryOrderAcquire, MemoryOrderRelaxed},
		{MemoryOrderAcquire, MemoryOrderAcquire},
		{MemoryOrderRelease, MemoryOrderRelaxed},
		{MemoryOrderAcqRel, MemoryOrderRelaxed},
		{MemoryOrderAcqRel, MemoryOrderAcquire},
		{MemoryOrderSeqCst, MemoryOrderRelaxed},
		{MemoryOrderSeqCst, MemoryOrderAcquire},
		{MemoryOrderSeqCst, MemoryOrderSeqCst},
	}
	for _, pair := range legal {
		if !LegalCompareExchangeOrders(pair[0], pair[1]) {
			t.Fatalf("legal CAS pair rejected: success=%s failure=%s", pair[0], pair[1])
		}
	}

	illegal := [][2]MemoryOrder{
		{MemoryOrderRelaxed, MemoryOrderAcquire},
		{MemoryOrderRelaxed, MemoryOrderRelease},
		{MemoryOrderAcquire, MemoryOrderSeqCst},
		{MemoryOrderRelease, MemoryOrderAcquire},
		{MemoryOrderAcqRel, MemoryOrderSeqCst},
		{MemoryOrderSeqCst, MemoryOrderRelease},
		{MemoryOrderSeqCst, MemoryOrderAcqRel},
	}
	for _, pair := range illegal {
		if LegalCompareExchangeOrders(pair[0], pair[1]) {
			t.Fatalf("illegal CAS pair accepted: success=%s failure=%s", pair[0], pair[1])
		}
	}
}

func TestCompareExchangeSurfaceIsExactlyLegalPairs(t *testing.T) {
	names := []string{
		"atomic_compare_exchange_relaxed_relaxed",
		"atomic_compare_exchange_acquire_relaxed",
		"atomic_compare_exchange_acquire_acquire",
		"atomic_compare_exchange_release_relaxed",
		"atomic_compare_exchange_acq_rel_relaxed",
		"atomic_compare_exchange_acq_rel_acquire",
		"atomic_compare_exchange_seq_cst_relaxed",
		"atomic_compare_exchange_seq_cst_acquire",
		"atomic_compare_exchange_seq_cst_seq_cst",
	}
	for _, name := range names {
		spec, ok := LookupAtomicBuiltin(name)
		if !ok || spec.Kind != AtomicBuiltinCompareExchange || !spec.Legal() {
			t.Fatalf("CAS builtin %s missing or illegal: %+v", name, spec)
		}
		if spec.Arity != 3 || !spec.ReturnsValue() {
			t.Fatalf("CAS builtin %s has wrong surface contract: %+v", name, spec)
		}
		if _, err := spec.Effect(); err != nil {
			t.Fatalf("CAS builtin %s has invalid effect: %v", name, err)
		}
	}

	for _, name := range []string{
		"atomic_compare_exchange_relaxed_acquire",
		"atomic_compare_exchange_release_acquire",
		"atomic_compare_exchange_acq_rel_seq_cst",
		"atomic_compare_exchange_seq_cst_release",
		"atomic_compare_exchange_seq_cst_acq_rel",
	} {
		if _, ok := LookupAtomicBuiltin(name); ok {
			t.Fatalf("illegal CAS source builtin unexpectedly exists: %s", name)
		}
	}
}

func TestCompareExchangeLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		spec, ok := LookupAtomicBuiltin("atomic_compare_exchange_acq_rel_acquire")
		if !ok || !spec.Legal() {
			panic("CAS lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("CAS semantic lookup allocated %.2f objects per call; want zero", allocs)
	}
}
