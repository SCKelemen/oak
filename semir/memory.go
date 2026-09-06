package semir

import "fmt"

// TypeAtomic is the semantic type of one atomic machine cell. The carrier is
// stored in Type.Base so Atomic[u32] is represented as Type{Kind: TypeAtomic,
// Base: "u32"}. Atomicity is an access contract attached to storage identity;
// a value loaded from the cell is an ordinary carrier value.
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
// order. Compare-exchange is intentionally separate future work because it has
// independent success/failure orders and failure-side value-update semantics.
type AtomicOperation string

const (
	AtomicLoad  AtomicOperation = "load"
	AtomicStore AtomicOperation = "store"
	AtomicRMW   AtomicOperation = "rmw"
	AtomicFence AtomicOperation = "fence"
)

// LegalAtomicOrder encodes the v1 order matrix. Illegal combinations are a
// language error, not a backend choice.
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
		return order != MemoryOrderRelaxed
	default:
		return false
	}
}

// AtomicBuiltinKind identifies the exact source operation while AtomicOperation
// captures the memory-model class shared by proofs/effects.
type AtomicBuiltinKind uint8

const (
	AtomicBuiltinInvalid AtomicBuiltinKind = iota
	AtomicBuiltinLoad
	AtomicBuiltinStore
	AtomicBuiltinFetchAdd
	AtomicBuiltinFence
)

// AtomicBuiltinSpec is the single semantic descriptor used by the checker,
// evaluator, and backend. Arity and order are compile-time facts. Lookup uses a
// switch rather than a map so the compiler's hot semantic lookup path performs
// no heap allocation and has no initialization state.
type AtomicBuiltinSpec struct {
	Name      string
	Kind      AtomicBuiltinKind
	Operation AtomicOperation
	Order     MemoryOrder
	Arity     uint8
}

func (s AtomicBuiltinSpec) ReturnsValue() bool {
	return s.Kind == AtomicBuiltinLoad || s.Kind == AtomicBuiltinFetchAdd
}

func (s AtomicBuiltinSpec) Effect() (Effect, error) {
	return AtomicEffect(s.Operation, s.Order)
}

// LookupAtomicBuiltin defines the complete v1 source surface. Order-specific
// names make illegal operation/order pairs unrepresentable rather than asking a
// runtime enum or backend fallback to reject them.
func LookupAtomicBuiltin(name string) (AtomicBuiltinSpec, bool) {
	switch name {
	case "atomic_load_relaxed":
		return AtomicBuiltinSpec{name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderRelaxed, 1}, true
	case "atomic_load_acquire":
		return AtomicBuiltinSpec{name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderAcquire, 1}, true
	case "atomic_load_seq_cst":
		return AtomicBuiltinSpec{name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderSeqCst, 1}, true
	case "atomic_store_relaxed":
		return AtomicBuiltinSpec{name, AtomicBuiltinStore, AtomicStore, MemoryOrderRelaxed, 2}, true
	case "atomic_store_release":
		return AtomicBuiltinSpec{name, AtomicBuiltinStore, AtomicStore, MemoryOrderRelease, 2}, true
	case "atomic_store_seq_cst":
		return AtomicBuiltinSpec{name, AtomicBuiltinStore, AtomicStore, MemoryOrderSeqCst, 2}, true
	case "atomic_fetch_add_relaxed":
		return AtomicBuiltinSpec{name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderRelaxed, 2}, true
	case "atomic_fetch_add_acquire":
		return AtomicBuiltinSpec{name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderAcquire, 2}, true
	case "atomic_fetch_add_release":
		return AtomicBuiltinSpec{name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderRelease, 2}, true
	case "atomic_fetch_add_acq_rel":
		return AtomicBuiltinSpec{name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderAcqRel, 2}, true
	case "atomic_fetch_add_seq_cst":
		return AtomicBuiltinSpec{name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderSeqCst, 2}, true
	case "atomic_fence_acquire":
		return AtomicBuiltinSpec{name, AtomicBuiltinFence, AtomicFence, MemoryOrderAcquire, 0}, true
	case "atomic_fence_release":
		return AtomicBuiltinSpec{name, AtomicBuiltinFence, AtomicFence, MemoryOrderRelease, 0}, true
	case "atomic_fence_acq_rel":
		return AtomicBuiltinSpec{name, AtomicBuiltinFence, AtomicFence, MemoryOrderAcqRel, 0}, true
	case "atomic_fence_seq_cst":
		return AtomicBuiltinSpec{name, AtomicBuiltinFence, AtomicFence, MemoryOrderSeqCst, 0}, true
	default:
		return AtomicBuiltinSpec{}, false
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
