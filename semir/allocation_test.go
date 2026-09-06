package semir

import (
	"strings"
	"testing"
)

func TestAllocatorModelValidatesArenaAndSlab(t *testing.T) {
	module := Module{Allocators: []Allocator{
		{Name: "request", Kind: AllocationArena, Region: "Request"},
		{Name: "tasks", Kind: AllocationSlab, ElementType: "Task", Capacity: 1024},
	}}
	if err := module.Validate(); err != nil {
		t.Fatalf("valid allocator model rejected: %v", err)
	}
}

func TestBoundedSlabRequiresCapacity(t *testing.T) {
	err := (Allocator{Name: "tasks", Kind: AllocationSlab, ElementType: "Task"}).Validate()
	if err == nil || !strings.Contains(err.Error(), "static capacity") {
		t.Fatalf("expected missing-capacity error, got %v", err)
	}
}

func TestBroadAllocationForbidConflictsWithScopedAllocation(t *testing.T) {
	authority := Authority{
		RequiredEffects:  []Effect{AllocationEffect("request")},
		ForbiddenEffects: []Effect{AnyAllocationEffect()},
	}
	if err := authority.Validate(); err == nil || !strings.Contains(err.Error(), "both required and forbidden") {
		t.Fatalf("expected broad/scoped allocation conflict, got %v", err)
	}
}

func TestDifferentScopedAllocationsDoNotConflict(t *testing.T) {
	authority := Authority{
		RequiredEffects:  []Effect{AllocationEffect("request")},
		ForbiddenEffects: []Effect{AllocationEffect("audio_rt")},
	}
	if err := authority.Validate(); err != nil {
		t.Fatalf("independent allocator effects conflicted: %v", err)
	}
}
