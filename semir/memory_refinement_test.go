package semir

import (
	"reflect"
	"testing"
)

// The atomic order tables and the source builtin catalogue are stated in
// spec/lean/Oak/MemoryOrderRefinement.lean as explicit tables proved by
// decide against Oak.MemoryOrder. This test pins the same tables against
// the Go decision procedures, so the two pins are the correspondence: a
// change to either side has to visit the other. Rows and columns follow
// the Lean enumeration: relaxed, acquire, release, acq-rel, seq-cst.

var refinementOrders = []MemoryOrder{MemoryOrderRelaxed, MemoryOrderAcquire, MemoryOrderRelease, MemoryOrderAcqRel, MemoryOrderSeqCst}

// legalTable mirrors Oak.MemoryOrderRefinement.legal_table.
var legalTable = map[AtomicOperation][]bool{
	AtomicLoad:  {true, true, false, false, true},
	AtomicStore: {true, false, true, false, true},
	AtomicRMW:   {true, true, true, true, true},
	AtomicFence: {false, true, true, true, true},
}

// casTable mirrors Oak.MemoryOrderRefinement.cas_table: rows are success
// orders, columns failure orders.
var casTable = [][]bool{
	{true, false, false, false, false},
	{true, true, false, false, false},
	{true, false, false, false, false},
	{true, true, false, false, false},
	{true, true, false, false, true},
}

func TestLegalAtomicOrderMatchesLeanTable(t *testing.T) {
	for op, want := range legalTable {
		got := make([]bool, len(refinementOrders))
		for i, order := range refinementOrders {
			got[i] = LegalAtomicOrder(op, order)
		}
		if !reflect.DeepEqual(got, want) {
			t.Fatalf("LegalAtomicOrder(%s) row = %v, want %v (Oak.MemoryOrderRefinement.legal_table)", op, got, want)
		}
	}
	for _, order := range refinementOrders {
		if LegalAtomicOrder(AtomicCompareExchange, order) {
			t.Fatalf("compare-exchange accepted as a single-order operation at %s", order)
		}
	}
	if LegalAtomicOrder(AtomicLoad, MemoryOrder("mystery")) {
		t.Fatal("unknown order accepted")
	}
}

func TestLegalCompareExchangeMatchesLeanTable(t *testing.T) {
	for i, success := range refinementOrders {
		for j, failure := range refinementOrders {
			if got := LegalCompareExchangeOrders(success, failure); got != casTable[i][j] {
				t.Fatalf("LegalCompareExchangeOrders(%s, %s) = %v, want %v (Oak.MemoryOrderRefinement.cas_table)", success, failure, got, casTable[i][j])
			}
		}
	}
}

// catalogueEntry mirrors Oak.MemoryOrderRefinement.Entry.
type catalogueEntry struct {
	name    string
	op      AtomicOperation
	order   MemoryOrder
	failure MemoryOrder // "" for every family but compare-exchange
}

// catalogue mirrors Oak.MemoryOrderRefinement.catalogue, in its order.
var catalogue = []catalogueEntry{
	{"atomic_load_relaxed", AtomicLoad, MemoryOrderRelaxed, ""},
	{"atomic_load_acquire", AtomicLoad, MemoryOrderAcquire, ""},
	{"atomic_load_seq_cst", AtomicLoad, MemoryOrderSeqCst, ""},
	{"atomic_store_relaxed", AtomicStore, MemoryOrderRelaxed, ""},
	{"atomic_store_release", AtomicStore, MemoryOrderRelease, ""},
	{"atomic_store_seq_cst", AtomicStore, MemoryOrderSeqCst, ""},
	{"atomic_fetch_add_relaxed", AtomicRMW, MemoryOrderRelaxed, ""},
	{"atomic_fetch_add_acquire", AtomicRMW, MemoryOrderAcquire, ""},
	{"atomic_fetch_add_release", AtomicRMW, MemoryOrderRelease, ""},
	{"atomic_fetch_add_acq_rel", AtomicRMW, MemoryOrderAcqRel, ""},
	{"atomic_fetch_add_seq_cst", AtomicRMW, MemoryOrderSeqCst, ""},
	{"atomic_exchange_relaxed", AtomicRMW, MemoryOrderRelaxed, ""},
	{"atomic_exchange_acquire", AtomicRMW, MemoryOrderAcquire, ""},
	{"atomic_exchange_release", AtomicRMW, MemoryOrderRelease, ""},
	{"atomic_exchange_acq_rel", AtomicRMW, MemoryOrderAcqRel, ""},
	{"atomic_exchange_seq_cst", AtomicRMW, MemoryOrderSeqCst, ""},
	{"atomic_compare_exchange_relaxed_relaxed", AtomicCompareExchange, MemoryOrderRelaxed, MemoryOrderRelaxed},
	{"atomic_compare_exchange_acquire_relaxed", AtomicCompareExchange, MemoryOrderAcquire, MemoryOrderRelaxed},
	{"atomic_compare_exchange_acquire_acquire", AtomicCompareExchange, MemoryOrderAcquire, MemoryOrderAcquire},
	{"atomic_compare_exchange_release_relaxed", AtomicCompareExchange, MemoryOrderRelease, MemoryOrderRelaxed},
	{"atomic_compare_exchange_acq_rel_relaxed", AtomicCompareExchange, MemoryOrderAcqRel, MemoryOrderRelaxed},
	{"atomic_compare_exchange_acq_rel_acquire", AtomicCompareExchange, MemoryOrderAcqRel, MemoryOrderAcquire},
	{"atomic_compare_exchange_seq_cst_relaxed", AtomicCompareExchange, MemoryOrderSeqCst, MemoryOrderRelaxed},
	{"atomic_compare_exchange_seq_cst_acquire", AtomicCompareExchange, MemoryOrderSeqCst, MemoryOrderAcquire},
	{"atomic_compare_exchange_seq_cst_seq_cst", AtomicCompareExchange, MemoryOrderSeqCst, MemoryOrderSeqCst},
	{"atomic_fence_acquire", AtomicFence, MemoryOrderAcquire, ""},
	{"atomic_fence_release", AtomicFence, MemoryOrderRelease, ""},
	{"atomic_fence_acq_rel", AtomicFence, MemoryOrderAcqRel, ""},
	{"atomic_fence_seq_cst", AtomicFence, MemoryOrderSeqCst, ""},
}

func TestAtomicBuiltinCatalogueMatchesLean(t *testing.T) {
	if len(catalogue) != 29 {
		t.Fatalf("catalogue has %d entries, Oak.MemoryOrderRefinement.catalogue_size says 29", len(catalogue))
	}
	seen := map[string]bool{}
	for _, entry := range catalogue {
		if seen[entry.name] {
			t.Fatalf("%s listed twice", entry.name)
		}
		seen[entry.name] = true
		spec, ok := LookupAtomicBuiltin(entry.name)
		if !ok {
			t.Fatalf("%s: not a source builtin", entry.name)
		}
		if spec.Operation != entry.op || spec.Order != entry.order || spec.FailureOrder != entry.failure {
			t.Fatalf("%s: Go spec (%s, %s, %q) differs from the Lean catalogue (%s, %s, %q)", entry.name, spec.Operation, spec.Order, spec.FailureOrder, entry.op, entry.order, entry.failure)
		}
		if !spec.Legal() {
			t.Fatalf("%s: Go rejects a builtin Oak.MemoryOrderRefinement.catalogue_legal admits", entry.name)
		}
		if (spec.FailureOrder != "") != (spec.Operation == AtomicCompareExchange) {
			t.Fatalf("%s: failure order set outside the compare-exchange family", entry.name)
		}
	}
	// No source builtin outside the catalogue: every name the Go side spells
	// for these families is listed.
	for _, family := range []string{"atomic_load", "atomic_store", "atomic_fetch_add", "atomic_exchange", "atomic_fence"} {
		for _, suffix := range []string{"relaxed", "acquire", "release", "acq_rel", "seq_cst"} {
			name := family + "_" + suffix
			_, ok := LookupAtomicBuiltin(name)
			if ok != seen[name] {
				t.Fatalf("%s: Go defines it %v, Lean catalogue lists it %v", name, ok, seen[name])
			}
		}
	}
}
