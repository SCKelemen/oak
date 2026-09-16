package compiler

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func TestCheckedGlobalMemoryProjectsThroughDAGAndEliminatesOverwrittenStore(t *testing.T) {
	module, err := New().WithSource("optir_memory.oak", `
counter: u32 = u32(0)

replace: (x: u32): u32 {
  counter = x
  counter = x + u32(1)
  counter
}

main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	replace, ok := optIRFunction(module, "replace")
	if !ok {
		t.Fatalf("replace was not projected: %+v", module.Refusals)
	}
	if replace.CheckedMemoryHash == "" || replace.CheckedMemoryHash != replace.CheckedMemory.Fingerprint() {
		t.Fatalf("checked memory authority fingerprint = %q / %q", replace.CheckedMemoryHash, replace.CheckedMemory.Fingerprint())
	}
	regions := replace.MemoryProjection.Metadata.Regions
	if len(regions) != 1 || regions[0] == "" ||
		!reflect.DeepEqual(replace.MemoryProjection.Observability.LiveOut, []optir.RegionID{regions[0]}) {
		t.Fatalf("checked memory projection = %+v", replace.MemoryProjection)
	}
	if err := optir.VerifyCheckedMemoryProjection(replace.LoopInvariant, replace.CheckedMemory, replace.MemoryProjection); err != nil {
		t.Fatalf("checked memory projection verification: %v", err)
	}
	if len(replace.DeadStoreElimination.Removed) != 1 || replace.DeadStoreElimination.Removed[0].Region != regions[0] {
		t.Fatalf("dead-store report = %+v", replace.DeadStoreElimination)
	}
	if err := optir.VerifyDeadStoreElimination(
		replace.LoopInvariant,
		replace.MemoryProjection.Metadata,
		replace.MemorySSA,
		replace.MemoryProjection.Observability,
		replace.MemoryLiveness,
		replace.DeadStores,
		replace.DeadStoreMetadata,
		replace.DeadStoreElimination,
	); err != nil {
		t.Fatalf("dead-store verification: %v", err)
	}
	if stores, loads := countOptIRMemoryOperations(replace.LoopInvariant); stores != 2 || loads != 1 {
		t.Fatalf("pre-DSE memory operations = stores %d, loads %d", stores, loads)
	}
	if stores, loads := countOptIRMemoryOperations(replace.DeadStores); stores != 1 || loads != 1 {
		t.Fatalf("post-DSE memory operations = stores %d, loads %d", stores, loads)
	}
	projected, err := optir.ProjectCheckedMemory(replace.DeadStores, replace.CheckedMemory)
	if err != nil {
		t.Fatalf("post-DSE checked memory projection: %v", err)
	}
	if !reflect.DeepEqual(projected.Metadata, replace.DeadStoreMetadata) {
		t.Fatalf("post-DSE metadata = %+v, want %+v", projected.Metadata, replace.DeadStoreMetadata)
	}
}

func TestCheckedGlobalMemoryKeepsBranchStoresAndRejectsAggregateGlobals(t *testing.T) {
	module, err := New().WithSource("optir_memory_branch.oak", `
flag: Bool = false
items: [2]u32

choose: (value: Bool): Bool {
  value ? {
    flag = true
  } | {
    flag = false
  }
  flag
}

read_item: (): u32 = items[u32(0)]

identity: (value: Bool): Bool = value
mixed: (value: Bool): Bool {
  flag = identity(value)
  flag
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	choose, ok := optIRFunction(module, "choose")
	if !ok {
		t.Fatalf("choose was not projected: %+v", module.Refusals)
	}
	if len(choose.MemoryProjection.Metadata.Operations) != 3 || len(choose.DeadStoreElimination.Removed) != 0 {
		t.Fatalf("branch memory analysis = projection %+v, DSE %+v", choose.MemoryProjection, choose.DeadStoreElimination)
	}
	if _, ok := optIRFunction(module, "read_item"); ok {
		t.Fatal("aggregate global unexpectedly entered the closed scalar memory vocabulary")
	}
	if _, ok := optIRFunction(module, "mixed"); ok {
		t.Fatal("call mixed with global state unexpectedly entered memory analysis")
	}
	foundMixedRefusal := false
	for _, refusal := range module.Refusals {
		if refusal.Function == "mixed" && strings.Contains(refusal.Reason, "interprocedural effect summaries") {
			foundMixedRefusal = true
		}
	}
	if !foundMixedRefusal {
		t.Fatalf("mixed call/global refusal = %+v", module.Refusals)
	}
}

func countOptIRMemoryOperations(cfg optir.CFG) (stores, loads int) {
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			switch operation.Code {
			case optir.OpStoreRegion:
				stores++
			case optir.OpLoadRegion:
				loads++
			}
		}
	}
	return stores, loads
}
