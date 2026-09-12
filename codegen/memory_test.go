package codegen

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func TestCMemoryOrderMapping(t *testing.T) {
	cases := []struct {
		order semir.MemoryOrder
		want  string
	}{
		{semir.MemoryOrderRelaxed, "memory_order_relaxed"},
		{semir.MemoryOrderAcquire, "memory_order_acquire"},
		{semir.MemoryOrderRelease, "memory_order_release"},
		{semir.MemoryOrderAcqRel, "memory_order_acq_rel"},
		{semir.MemoryOrderSeqCst, "memory_order_seq_cst"},
	}
	for _, tc := range cases {
		got, err := cMemoryOrder(tc.order)
		if err != nil {
			t.Fatalf("cMemoryOrder(%q): %v", tc.order, err)
		}
		if got != tc.want {
			t.Fatalf("cMemoryOrder(%q) = %q, want %q", tc.order, got, tc.want)
		}
	}
	if _, err := cMemoryOrder(semir.MemoryOrder("mystery")); err == nil {
		t.Fatal("unknown order unexpectedly accepted")
	}
}

func TestAtomicCTypeIsExactCarrier(t *testing.T) {
	got, err := atomicCType("u32")
	if err != nil {
		t.Fatal(err)
	}
	if got != "_Atomic(u32)" {
		t.Fatalf("unexpected atomic type: %s", got)
	}
	if _, err := atomicCType("uptr"); err == nil {
		t.Fatal("pointer/native carrier unexpectedly accepted")
	}
}

func TestAtomicLoadStoreRejectIllegalOrders(t *testing.T) {
	if _, err := atomicLoadC("&x", semir.MemoryOrderRelease); err == nil {
		t.Fatal("release load unexpectedly accepted")
	}
	if _, err := atomicStoreC("&x", "7", semir.MemoryOrderAcquire); err == nil {
		t.Fatal("acquire store unexpectedly accepted")
	}
	load, err := atomicLoadC("&x", semir.MemoryOrderAcquire)
	if err != nil {
		t.Fatal(err)
	}
	if load != "atomic_load_explicit(&x, memory_order_acquire)" {
		t.Fatalf("unexpected load lowering: %s", load)
	}
	store, err := atomicStoreC("&x", "7", semir.MemoryOrderRelease)
	if err != nil {
		t.Fatal(err)
	}
	if store != "atomic_store_explicit(&x, 7, memory_order_release)" {
		t.Fatalf("unexpected store lowering: %s", store)
	}
}

func TestAtomicRMWAndFenceLowering(t *testing.T) {
	exchange, err := atomicExchangeC("&x", "9", semir.MemoryOrderAcqRel)
	if err != nil {
		t.Fatal(err)
	}
	if exchange != "atomic_exchange_explicit(&x, 9, memory_order_acq_rel)" {
		t.Fatalf("unexpected exchange lowering: %s", exchange)
	}
	add, err := atomicFetchAddC("&x", "1", semir.MemoryOrderRelaxed)
	if err != nil {
		t.Fatal(err)
	}
	if add != "atomic_fetch_add_explicit(&x, 1, memory_order_relaxed)" {
		t.Fatalf("unexpected fetch-add lowering: %s", add)
	}
	if _, err := atomicFenceC(semir.MemoryOrderRelaxed); err == nil {
		t.Fatal("relaxed fence unexpectedly accepted")
	}
	fence, err := atomicFenceC(semir.MemoryOrderSeqCst)
	if err != nil {
		t.Fatal(err)
	}
	if fence != "atomic_thread_fence(memory_order_seq_cst)" {
		t.Fatalf("unexpected fence lowering: %s", fence)
	}
}

func TestVolatileLoweringDoesNotInventFence(t *testing.T) {
	read, err := volatileReadC("u32", "addr")
	if err != nil {
		t.Fatal(err)
	}
	if read != "(*(volatile u32 *)(addr))" {
		t.Fatalf("unexpected volatile read lowering: %s", read)
	}
	write, err := volatileWriteC("u32", "addr", "value")
	if err != nil {
		t.Fatal(err)
	}
	if write != "(*(volatile u32 *)(addr) = (value))" {
		t.Fatalf("unexpected volatile write lowering: %s", write)
	}
	if strings.Contains(read+write, "fence") || strings.Contains(read+write, "barrier") {
		t.Fatal("raw volatile lowering must not invent synchronization")
	}
}

// Lock-free admission consults the C11 macro for each carrier's width, and
// only where the C type actually has that width (docs/spec/65 §6).
func TestLockFreeConditionPerWidth(t *testing.T) {
	cases := map[string]string{
		"u8":  "ATOMIC_CHAR_LOCK_FREE == 2",
		"i16": "ATOMIC_SHORT_LOCK_FREE == 2",
		"u32": "(sizeof(int) != 4 || ATOMIC_INT_LOCK_FREE == 2) && (sizeof(long) != 4 || ATOMIC_LONG_LOCK_FREE == 2)",
		"i64": "(sizeof(long) != 8 || ATOMIC_LONG_LOCK_FREE == 2) && (sizeof(long long) != 8 || ATOMIC_LLONG_LOCK_FREE == 2)",
	}
	for carrier, want := range cases {
		got, err := lockFreeConditionC(carrier)
		if err != nil {
			t.Fatalf("lockFreeConditionC(%q): %v", carrier, err)
		}
		if got != want {
			t.Fatalf("lockFreeConditionC(%q) = %q, want %q", carrier, got, want)
		}
	}
	if _, err := lockFreeConditionC("f32"); err == nil {
		t.Fatal("non-integer carrier unexpectedly admitted")
	}
}

func TestAtomicAdmissionEmitsOnlyRecordedCarriers(t *testing.T) {
	cg := &CodeGenerator{}
	cg.emitAtomicAdmission()
	if cg.output.Len() != 0 {
		t.Fatalf("admission emitted without atomics:\n%s", cg.output.String())
	}
	cg.atomicsIncluded = true
	cg.atomicCarriers = map[string]bool{"i8": true, "u64": true}
	cg.emitAtomicAdmission()
	out := cg.output.String()
	for _, want := range []string{
		"#if !defined(OAK_ATOMIC_ACCEPT_LOCKED)",
		"typedef char oak_atomic_lock_free_i8[ (ATOMIC_CHAR_LOCK_FREE == 2) ? 1 : -1 ];",
		"typedef char oak_atomic_lock_free_u64[",
		"#endif",
	} {
		if !strings.Contains(out, want) {
			t.Fatalf("admission block lacks %q:\n%s", want, out)
		}
	}
	if strings.Contains(out, "oak_atomic_lock_free_u32") {
		t.Fatalf("unrecorded carrier asserted:\n%s", out)
	}
}

func TestAtomicAdmissionStrictDropsOptOut(t *testing.T) {
	cg := &CodeGenerator{atomicsIncluded: true, atomicCarriers: map[string]bool{"u32": true}}
	cg.SetStrictAdmission(true)
	cg.emitAtomicAdmission()
	out := cg.output.String()
	if strings.Contains(out, "OAK_ATOMIC_ACCEPT_LOCKED") || strings.Contains(out, "#if") || strings.Contains(out, "#endif") {
		t.Fatalf("strict admission kept a preprocessor opt-out:\n%s", out)
	}
	if !strings.Contains(out, "typedef char oak_atomic_lock_free_u32[") {
		t.Fatalf("strict admission lost the assertion:\n%s", out)
	}
}
