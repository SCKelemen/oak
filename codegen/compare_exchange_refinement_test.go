package codegen

import (
	"strings"
	"testing"
)

// The strong compare-exchange helper is transliterated in
// spec/lean/Oak/CompareExchangeRefinement.lean, where it is proved to meet
// the value-oriented contract of docs/spec/65-machine-memory.md §3 over
// C11's mutable-expected primitive. That proof is about the text below;
// this test pins the emitted helper to it, so a change to either side has
// to visit the other.
func TestCompareExchangeHelperMatchesLeanTransliteration(t *testing.T) {
	output := generateC(t, "package main\n\ncell: Atomic[u32]\n\nmain: (): i32 {\n  atomic_store_relaxed(cell, u32(1))\n  seen: u32 = atomic_compare_exchange_acq_rel_acquire(cell, u32(1), u32(2))\n  i32_bits_u32(atomic_load_acquire(cell) - seen - u32(1))\n}\n")
	want := "static inline u32 __oak_cas_u32_acq_rel_acquire(_Atomic(u32) *cell, u32 expected, u32 desired) {\n" +
		"  u32 observed = expected;\n" +
		"  (void)atomic_compare_exchange_strong_explicit(cell, &observed, desired, OAK_ORDER_CAS_ACQ_REL, memory_order_acquire);\n" +
		"  return observed;\n" +
		"}\n"
	if !strings.Contains(output, want) {
		t.Fatalf("emitted C lacks the pinned helper\n%s\n— update spec/lean/Oak/CompareExchangeRefinement.lean with it; output:\n%s", want, output)
	}
	if !strings.Contains(output, "/* strong compare-exchange: returns the value observed at the compare */") {
		t.Fatalf("helper comment missing:\n%s", output)
	}
}
