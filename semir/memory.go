package semir

import "fmt"

// TypeAtomic is the semantic type of one atomic machine value. The carrier is
// stored in Type.Base so Atomic[u32] is represented as Type{Kind: TypeAtomic,
// Base: "u32"}. Atomicity is an access contract, not a request for a different
// numeric value domain.
const TypeAtomic TypeKind = "atomic"

// MemoryOrder is Oak's language-level memory-order vocabulary. These names are
// semantic: backends must refine them to target/compiler operations with the
// same ordering guarantees rather than treating them as advisory metadata.
type MemoryOrder string

const (
	MemoryOrderRelaxed MemoryOrder = "relaxed"
	MemoryOrderAcquire MemoryOrder = "acquire"
	MemoryOrderRelease MemoryOrder = "release"
	MemoryOrderAcqRel  MemoryOrder = "acq-rel"
	MemoryOrderSeqCst  MemoryOrder = "seq-cst"
)

func (o MemoryOrder) Valid() bool {
	switch o {
	case MemoryOrderRelaxed, MemoryOrderAcquire, MemoryOrderRelease, MemoryOrderAcqRel, MemoryOrderSeqCst:
		return true
	default:
		return false
	}
}

// AtomicOperation classifies an atomic access independently of its memory
// order. Compare-exchange is intentionally deferred: its distinct success and
// failure orders deserve a separate contract instead of being squeezed into a
// single-order RMW operation.
type AtomicOperation string

const (
	AtomicLoad  AtomicOperation = "load"
	AtomicStore AtomicOperation = "store"
	AtomicRMW   AtomicOperation = "rmw"
	AtomicFence AtomicOperation = "fence"
)

// LegalAtomicOrder encodes the v1 order matrix. Illegal combinations are a
// language error, not a backend choice. In particular a load can never be
// release/acq-rel and a store can never be acquire/acq-rel.
func LegalAtomicOrder(op AtomicOperation, order MemoryOrder) bool {
	if !order.Valid() {
		return false
	}
	switch op {
	case AtomicLoad:
		return order == MemoryOrderRelaxed || order == MemoryOrderAcquire || order == MemoryOrderSeqCst
	case AtomicStore:
		return order == MemoryOrderRelaxed || order == MemoryOrderRelease || order == MemoryOrderSeqCst
	case AtomicRMW:
		return true
	case AtomicFence:
		// A relaxed fence has no synchronization effect and is excluded from
		// the surface rather than pretending to be useful.
		return order != MemoryOrderRelaxed
	default:
		return false
	}
}

// AtomicEffect projects an atomic operation into Oak's authority/effect axis.
// The order is retained as a parameter so verification, documentation, and
// future scheduling/debug tooling do not need to recover it from syntax.
func AtomicEffect(op AtomicOperation, order MemoryOrder) (Effect, error) {
	if !LegalAtomicOrder(op, order) {
		return Effect{}, fmt.Errorf("illegal atomic memory order %q for %q", order, op)
	}
	name := ""
	switch op {
	case AtomicLoad:
		name = "AtomicLoad"
	case AtomicStore:
		name = "AtomicStore"
	case AtomicRMW:
		name = "AtomicRMW"
	case AtomicFence:
		name = "AtomicFence"
	}
	return Effect{Namespace: "Memory", Name: name, Parameters: []string{string(order)}}, nil
}

// AtomicCarrierAllowed is deliberately narrow for the first executable
// systems slice. Fixed-width integers have unambiguous machine width and C11
// atomic carriers. Pointer atomics, aggregate atomics, and target-dependent
// int/uint are separate future contracts rather than accidental extensions.
func AtomicCarrierAllowed(base string) bool {
	switch base {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
		return true
	default:
		return false
	}
}

// ValidateAtomicType checks the semantic portion of Atomic[T]. Layout-specific
// lock-freedom is a target property and is intentionally not claimed here.
func ValidateAtomicType(t Type) error {
	if t.Kind != TypeAtomic {
		return fmt.Errorf("expected atomic type, got %q", t.Kind)
	}
	if !AtomicCarrierAllowed(t.Base) {
		return fmt.Errorf("Atomic[%s] is not a v1 atomic carrier", t.Base)
	}
	return nil
}

// VolatileOperation models exactly-one observable accesses. Volatile is not a
// synchronization primitive and, by itself, is not a complete device-MMIO
// ordering contract on architectures such as AArch64.
type VolatileOperation string

const (
	VolatileRead  VolatileOperation = "read"
	VolatileWrite VolatileOperation = "write"
)

func VolatileEffect(op VolatileOperation) (Effect, error) {
	switch op {
	case VolatileRead:
		return Effect{Namespace: "Memory", Name: "VolatileRead"}, nil
	case VolatileWrite:
		return Effect{Namespace: "Memory", Name: "VolatileWrite"}, nil
	default:
		return Effect{}, fmt.Errorf("unknown volatile operation %q", op)
	}
}
