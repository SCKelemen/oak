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
// order. Compare-exchange is a distinct class because it has independent
// success/failure orders.
type AtomicOperation string

const (
	AtomicLoad            AtomicOperation = "load"
	AtomicStore           AtomicOperation = "store"
	AtomicRMW             AtomicOperation = "rmw"
	AtomicCompareExchange AtomicOperation = "compare-exchange"
	AtomicFence           AtomicOperation = "fence"
)

// LegalAtomicOrder encodes the single-order v1 matrix. Compare-exchange must
// use LegalCompareExchangeOrders because its two orders are related.
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

// LegalCompareExchangeOrders is Oak's strong compare-exchange order relation.
// Failure never performs a write, so release/acq-rel failure orders are
// forbidden. Failure may also not be stronger than the success order.
func LegalCompareExchangeOrders(success, failure MemoryOrder) bool {
	if !success.Valid() || !failure.Valid() {
		return false
	}
	if failure == MemoryOrderRelease || failure == MemoryOrderAcqRel {
		return false
	}
	switch success {
	case MemoryOrderRelaxed:
		return failure == MemoryOrderRelaxed
	case MemoryOrderAcquire:
		return failure == MemoryOrderRelaxed || failure == MemoryOrderAcquire
	case MemoryOrderRelease:
		return failure == MemoryOrderRelaxed
	case MemoryOrderAcqRel:
		return failure == MemoryOrderRelaxed || failure == MemoryOrderAcquire
	case MemoryOrderSeqCst:
		return failure == MemoryOrderRelaxed || failure == MemoryOrderAcquire || failure == MemoryOrderSeqCst
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
	AtomicBuiltinExchange
	AtomicBuiltinCompareExchange
	AtomicBuiltinFence
)

// AtomicBuiltinSpec is the single semantic descriptor used by the checker,
// evaluator, and backend. Order and FailureOrder are compile-time facts.
// FailureOrder is empty for every non-CAS builtin. Lookup uses a switch rather
// than a map so the compiler's hot semantic lookup path performs no heap
// allocation and has no initialization state.
type AtomicBuiltinSpec struct {
	Name         string
	Kind         AtomicBuiltinKind
	Operation    AtomicOperation
	Order        MemoryOrder
	FailureOrder MemoryOrder
	Arity        uint8
}

func (s AtomicBuiltinSpec) ReturnsValue() bool {
	return s.Kind == AtomicBuiltinLoad || s.Kind == AtomicBuiltinFetchAdd || s.Kind == AtomicBuiltinExchange || s.Kind == AtomicBuiltinCompareExchange
}

func (s AtomicBuiltinSpec) Legal() bool {
	if s.Kind == AtomicBuiltinCompareExchange {
		return LegalCompareExchangeOrders(s.Order, s.FailureOrder)
	}
	return LegalAtomicOrder(s.Operation, s.Order)
}

func (s AtomicBuiltinSpec) Effect() (Effect, error) {
	if s.Kind == AtomicBuiltinCompareExchange {
		return AtomicCompareExchangeEffect(s.Order, s.FailureOrder)
	}
	return AtomicEffect(s.Operation, s.Order)
}

func atomicBuiltin(name string, kind AtomicBuiltinKind, op AtomicOperation, order MemoryOrder, arity uint8) AtomicBuiltinSpec {
	return AtomicBuiltinSpec{Name: name, Kind: kind, Operation: op, Order: order, Arity: arity}
}

func compareExchangeBuiltin(name string, success, failure MemoryOrder) AtomicBuiltinSpec {
	return AtomicBuiltinSpec{
		Name:         name,
		Kind:         AtomicBuiltinCompareExchange,
		Operation:    AtomicCompareExchange,
		Order:        success,
		FailureOrder: failure,
		Arity:        3,
	}
}

// LookupAtomicBuiltin defines the complete source surface. Order-specific names
// make illegal operation/order pairs unrepresentable rather than asking a
// runtime enum or backend fallback to reject them. Compare-exchange names encode
// success order first and failure order second.
func LookupAtomicBuiltin(name string) (AtomicBuiltinSpec, bool) {
	switch name {
	case "atomic_load_relaxed":
		return atomicBuiltin(name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderRelaxed, 1), true
	case "atomic_load_acquire":
		return atomicBuiltin(name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderAcquire, 1), true
	case "atomic_load_seq_cst":
		return atomicBuiltin(name, AtomicBuiltinLoad, AtomicLoad, MemoryOrderSeqCst, 1), true
	case "atomic_store_relaxed":
		return atomicBuiltin(name, AtomicBuiltinStore, AtomicStore, MemoryOrderRelaxed, 2), true
	case "atomic_store_release":
		return atomicBuiltin(name, AtomicBuiltinStore, AtomicStore, MemoryOrderRelease, 2), true
	case "atomic_store_seq_cst":
		return atomicBuiltin(name, AtomicBuiltinStore, AtomicStore, MemoryOrderSeqCst, 2), true
	case "atomic_fetch_add_relaxed":
		return atomicBuiltin(name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderRelaxed, 2), true
	case "atomic_fetch_add_acquire":
		return atomicBuiltin(name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderAcquire, 2), true
	case "atomic_fetch_add_release":
		return atomicBuiltin(name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderRelease, 2), true
	case "atomic_fetch_add_acq_rel":
		return atomicBuiltin(name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderAcqRel, 2), true
	case "atomic_fetch_add_seq_cst":
		return atomicBuiltin(name, AtomicBuiltinFetchAdd, AtomicRMW, MemoryOrderSeqCst, 2), true

	// atomic_exchange: unconditional swap returning the prior value — the
	// wait-free RMW (one instruction, no retry), legal at every RMW order
	// (docs/spec/65-machine-memory.md section 2). The Vyukov MPSC producer
	// is its canonical consumer.
	case "atomic_exchange_relaxed":
		return atomicBuiltin(name, AtomicBuiltinExchange, AtomicRMW, MemoryOrderRelaxed, 2), true
	case "atomic_exchange_acquire":
		return atomicBuiltin(name, AtomicBuiltinExchange, AtomicRMW, MemoryOrderAcquire, 2), true
	case "atomic_exchange_release":
		return atomicBuiltin(name, AtomicBuiltinExchange, AtomicRMW, MemoryOrderRelease, 2), true
	case "atomic_exchange_acq_rel":
		return atomicBuiltin(name, AtomicBuiltinExchange, AtomicRMW, MemoryOrderAcqRel, 2), true
	case "atomic_exchange_seq_cst":
		return atomicBuiltin(name, AtomicBuiltinExchange, AtomicRMW, MemoryOrderSeqCst, 2), true

	case "atomic_compare_exchange_relaxed_relaxed":
		return compareExchangeBuiltin(name, MemoryOrderRelaxed, MemoryOrderRelaxed), true
	case "atomic_compare_exchange_acquire_relaxed":
		return compareExchangeBuiltin(name, MemoryOrderAcquire, MemoryOrderRelaxed), true
	case "atomic_compare_exchange_acquire_acquire":
		return compareExchangeBuiltin(name, MemoryOrderAcquire, MemoryOrderAcquire), true
	case "atomic_compare_exchange_release_relaxed":
		return compareExchangeBuiltin(name, MemoryOrderRelease, MemoryOrderRelaxed), true
	case "atomic_compare_exchange_acq_rel_relaxed":
		return compareExchangeBuiltin(name, MemoryOrderAcqRel, MemoryOrderRelaxed), true
	case "atomic_compare_exchange_acq_rel_acquire":
		return compareExchangeBuiltin(name, MemoryOrderAcqRel, MemoryOrderAcquire), true
	case "atomic_compare_exchange_seq_cst_relaxed":
		return compareExchangeBuiltin(name, MemoryOrderSeqCst, MemoryOrderRelaxed), true
	case "atomic_compare_exchange_seq_cst_acquire":
		return compareExchangeBuiltin(name, MemoryOrderSeqCst, MemoryOrderAcquire), true
	case "atomic_compare_exchange_seq_cst_seq_cst":
		return compareExchangeBuiltin(name, MemoryOrderSeqCst, MemoryOrderSeqCst), true

	case "atomic_fence_acquire":
		return atomicBuiltin(name, AtomicBuiltinFence, AtomicFence, MemoryOrderAcquire, 0), true
	case "atomic_fence_release":
		return atomicBuiltin(name, AtomicBuiltinFence, AtomicFence, MemoryOrderRelease, 0), true
	case "atomic_fence_acq_rel":
		return atomicBuiltin(name, AtomicBuiltinFence, AtomicFence, MemoryOrderAcqRel, 0), true
	case "atomic_fence_seq_cst":
		return atomicBuiltin(name, AtomicBuiltinFence, AtomicFence, MemoryOrderSeqCst, 0), true
	default:
		return AtomicBuiltinSpec{}, false
	}
}

// AtomicEffect projects a single-order atomic operation into Oak's
// authority/effect axis.
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

// AtomicCompareExchangeEffect retains both orders as semantic data so later
// happens-before proofs and tooling do not need to recover them from a name.
func AtomicCompareExchangeEffect(success, failure MemoryOrder) (Effect, error) {
	if !LegalCompareExchangeOrders(success, failure) {
		return Effect{}, fmt.Errorf("illegal compare-exchange orders success=%q failure=%q", success, failure)
	}
	return Effect{
		Namespace:  "Memory",
		Name:       "AtomicCompareExchange",
		Parameters: []string{string(success), string(failure)},
	}, nil
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
