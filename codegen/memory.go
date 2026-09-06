package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/semir"
)

// cMemoryOrder is the C11 projection of Oak's language-level ordering. This is
// deliberately a total checked conversion: a backend must never silently
// strengthen, weaken, or guess an unknown order.
func cMemoryOrder(order semir.MemoryOrder) (string, error) {
	switch order {
	case semir.MemoryOrderRelaxed:
		return "memory_order_relaxed", nil
	case semir.MemoryOrderAcquire:
		return "memory_order_acquire", nil
	case semir.MemoryOrderRelease:
		return "memory_order_release", nil
	case semir.MemoryOrderAcqRel:
		return "memory_order_acq_rel", nil
	case semir.MemoryOrderSeqCst:
		return "memory_order_seq_cst", nil
	default:
		return "", fmt.Errorf("unknown Oak memory order %q", order)
	}
}

// atomicCType returns the exact C11 atomic carrier used by the bootstrap C
// backend. _Atomic(T) preserves the fixed-width carrier chosen by Oak rather
// than substituting one of C's implementation-sized convenience typedefs.
func atomicCType(base string) (string, error) {
	if !semir.AtomicCarrierAllowed(base) {
		return "", fmt.Errorf("unsupported atomic C carrier %q", base)
	}
	return fmt.Sprintf("_Atomic(%s)", base), nil
}

func atomicLoadC(address string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicLoad, order) {
		return "", fmt.Errorf("illegal load order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_load_explicit(%s, %s)", address, cOrder), nil
}

func atomicStoreC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicStore, order) {
		return "", fmt.Errorf("illegal store order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_store_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicExchangeC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicRMW, order) {
		return "", fmt.Errorf("illegal exchange order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_exchange_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicFetchAddC(address, value string, order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicRMW, order) {
		return "", fmt.Errorf("illegal fetch-add order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_fetch_add_explicit(%s, %s, %s)", address, value, cOrder), nil
}

func atomicFenceC(order semir.MemoryOrder) (string, error) {
	if !semir.LegalAtomicOrder(semir.AtomicFence, order) {
		return "", fmt.Errorf("illegal fence order %q", order)
	}
	cOrder, err := cMemoryOrder(order)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("atomic_thread_fence(%s)", cOrder), nil
}

// volatileReadC/volatileWriteC model exactly one volatile access through an
// already-typed address expression. They intentionally emit no fence: volatile
// is observability, not inter-thread synchronization or a complete device-MMIO
// protocol.
func volatileReadC(cType, address string) string {
	return fmt.Sprintf("(*(volatile %s *)(%s))", cType, address)
}

func volatileWriteC(cType, address, value string) string {
	return fmt.Sprintf("(*(volatile %s *)(%s) = (%s))", cType, address, value)
}
