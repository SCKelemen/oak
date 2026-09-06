package semir

import "fmt"

// AllocationKind describes lifetime/storage policy without making allocators a
// special surface-language statement. Arena[R], Slab[T,N], etc. remain ordinary
// types; this descriptor carries facts needed by checking and projections.
type AllocationKind string

const (
	AllocationStack  AllocationKind = "stack"
	AllocationStatic AllocationKind = "static"
	AllocationCaller AllocationKind = "caller"
	AllocationArena  AllocationKind = "arena"
	AllocationSlab   AllocationKind = "slab"
	AllocationPool   AllocationKind = "pool"
	AllocationHeap   AllocationKind = "heap"
)

// Allocator is one semantically named allocation authority.
// Capacity == 0 means the capacity is supplied externally/not statically known;
// bounded slab/pool allocators require a non-zero capacity.
type Allocator struct {
	Name        string
	Kind        AllocationKind
	Region      string
	ElementType string
	Capacity    uint64
}

func (a Allocator) Validate() error {
	if a.Name == "" {
		return fmt.Errorf("allocator has empty name")
	}
	switch a.Kind {
	case AllocationStack, AllocationStatic, AllocationCaller, AllocationHeap:
		return nil
	case AllocationArena:
		if a.Region == "" {
			return fmt.Errorf("arena allocator %q has no region identity", a.Name)
		}
		return nil
	case AllocationSlab, AllocationPool:
		if a.ElementType == "" {
			return fmt.Errorf("%s allocator %q has no element type", a.Kind, a.Name)
		}
		if a.Capacity == 0 {
			return fmt.Errorf("%s allocator %q has no static capacity", a.Kind, a.Name)
		}
		return nil
	default:
		return fmt.Errorf("allocator %q has invalid allocation kind %q", a.Name, a.Kind)
	}
}

// AllocationEffect returns the effect of allocating from one named allocator.
func AllocationEffect(allocator string) Effect {
	if allocator == "" {
		return Effect{Namespace: "Memory", Name: "Allocate"}
	}
	return Effect{Namespace: "Memory", Name: "Allocate", Parameters: []string{allocator}}
}

// AnyAllocationEffect denotes allocation from any allocator. A broad forbidden
// effect overlaps parameterized AllocationEffect values during validation.
func AnyAllocationEffect() Effect {
	return Effect{Namespace: "Memory", Name: "Allocate"}
}

func BlockingEffect() Effect {
	return Effect{Namespace: "Thread", Name: "Block"}
}

func SyscallEffect() Effect {
	return Effect{Namespace: "Os", Name: "Syscall"}
}
