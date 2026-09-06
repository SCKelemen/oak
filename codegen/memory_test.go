package codegen

import (
	"testing"

	"github.com/SCKelemen/oak/semir"
)

func TestCMemoryOrder(t *testing.T) {
	cases := map[semir.MemoryOrder]string{
		semir.MemoryOrderRelaxed: "memory_order_relaxed",
		semir.MemoryOrderAcquire: "memory_order_acquire",
		semir.MemoryOrderRelease: "memory_order_release",
		semir.MemoryOrderAcqRel:  "memory_order_acq_rel",
		semir.MemoryOrderSeqCst:  "memory_order_seq_cst",
	}
	for order, want := range cases {
		got, err := cMemoryOrder(order)
		if err != nil {
			t.Fatalf("cMemoryOrder(%q): %v", order, err)
		}
		if got != want {
			t.Fatalf("cMemoryOrder(%q) = %q, want %q", order, got, want)
		}
	}
}

func TestAtomicCTypePreservesCarrier(t *testing.T) {
	got, err := atomicCType("u32")
	if err != nil {
		t.Fatal(err)
	}
	if got != "_Atomic(u32)" {
		t.Fatalf("unexpected C atomic type: %s", got)
	}
	if _, err := atomicCType("ptr"); err == nil {
		t.Fatal("pointer carrier unexpectedly accepted")
	}
}

func TestAtomicLoadLoweringRejectsRelease(t *testing.T) {
	if _, err := atomicLoadC("&x", semir.MemoryOrderRelease); err == nil {
		t.Fatal("release load unexpectedly accepted")
	}
	got, err := atomicLoadC("&x", semir.MemoryOrderAcquire)
	if err != nil {
		t.Fatal(err)
	}
	if got != "atomic_load_explicit(&x, memory_order_acquire)" {
		t.Fatalf("unexpected load lowering: %s", got)
	}
}

func TestAtomicStoreLoweringRejectsAcquire(t *testing.T) {
	if _, err := atomicStoreC("&x", "7", semir.MemoryOrderAcquire); err == nil {
		t.Fatal("acquire store unexpectedly accepted")
	}
	got, err := atomicStoreC("&x", "7", semir.MemoryOrderRelease)
	if err != nil {
		t.Fatal(err)
	}
	if got != "atomic_store_explicit(&x, 7, memory_order_release)" {
		t.Fatalf("unexpected store lowering: %s", got)
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
	if got := volatileReadC("u32", "addr"); got != "(*(volatile u32 *)(addr))" {
		t.Fatalf("unexpected volatile read lowering: %s", got)
	}
	if got := volatileWriteC("u32", "addr", "value"); got != "(*(volatile u32 *)(addr) = (value))" {
		t.Fatalf("unexpected volatile write lowering: %s", got)
	}
}
