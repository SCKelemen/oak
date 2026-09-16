package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

const optIRMemoryDeadStoreCleanupProgram = `
state: u32 = u32(0)
side: u32 = u32(0)

read_state: (): u32 = state

write_side: (value: u32): u32 {
  side = value
  value
}

after_forwarding: (value: u32): u32 {
  state = value + u32(1)
  answer: u32 = state
  state = u32(42)
  answer
}

after_pruning: (value: u32): u32 {
  state = value * u32(17)
  side = u32(20)
  answer: u32 = side == u32(20) ? u32(42) | read_state()
  state = u32(42)
  answer
}

keep_read: (value: u32): u32 {
  state = value * u32(17)
  answer: u32 = read_state()
  state = u32(42)
  answer
}

keep_branch_read: (flag: Bool, value: u32): u32 {
  state = value * u32(17)
  answer: u32 = flag ? read_state() | u32(42)
  state = u32(42)
  answer
}

keep_effect: (value: u32): u32 {
  state = write_side(value)
  unused: u32 = state
  state = u32(42)
  u32(42)
}

main: (): i32 =
  after_forwarding(u32(41)) == u32(42) && state == u32(42) &&
  after_pruning(u32(99)) == u32(42) && state == u32(42) && side == u32(20) &&
  keep_read(u32(2)) == u32(34) && state == u32(42) &&
  keep_branch_read(true, u32(2)) == u32(34) && state == u32(42) &&
  keep_branch_read(false, u32(99)) == u32(42) && state == u32(42) &&
  keep_effect(u32(99)) == u32(42) && state == u32(42) && side == u32(99) ? i32(42) | i32(1)
`

func TestCheckedGlobalMemoryCleanupEliminatesNewlyDeadStores(t *testing.T) {
	module, err := New().WithSource("cleanup_stores.oak", optIRMemoryDeadStoreCleanupProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, test := range []struct {
		name   string
		before int
		after  int
	}{
		{"after_forwarding", 2, 1},
		{"after_pruning", 3, 2},
		{"keep_read", 2, 2},
		{"keep_branch_read", 2, 2},
		{"keep_effect", 2, 1},
	} {
		t.Run(test.name, func(t *testing.T) {
			function, ok := optIRFunction(module, test.name)
			if !ok {
				t.Fatalf("function not projected: %+v", module.Refusals)
			}
			cleanup := function.MemoryCleanup
			if len(function.DeadStoreElimination.Removed) != 0 {
				t.Fatal("fixture must require the post-forwarding DSE opportunity")
			}
			if stores, _ := countOptIRMemoryOperations(cleanup.ScalarCFG); stores != test.before {
				t.Fatalf("pre-cleanup stores = %d, want %d", stores, test.before)
			}
			if stores, _ := countOptIRMemoryOperations(cleanup.CFG); stores != test.after || len(cleanup.DeadStoreElimination.Removed) != test.before-test.after {
				t.Fatalf("final stores = %d, want %d; DSE = %+v", stores, test.after, cleanup.DeadStoreElimination)
			}
			if err := verifyOptIRMemoryCleanup(function.ForwardedLoads, function.CheckedMemory, cleanup); err != nil {
				t.Fatal(err)
			}
			for _, cfg := range []optir.CFG{cleanup.SCCPSimplified, cleanup.ScalarCFG, cleanup.DeadStores, cleanup.DCECleaned, cleanup.CFG} {
				if err := optir.VerifyCFGCheckedFacts(cfg, function.CheckedFacts); err != nil {
					t.Fatal(err)
				}
			}
			projection, memorySSA, err := checkedOptIRMemoryState(cleanup.ScalarCFG, function.CheckedMemory)
			if err != nil {
				t.Fatal(err)
			}
			liveness, err := optir.AnalyzeMemoryDefinitionLiveness(cleanup.ScalarCFG, projection.Metadata, memorySSA, projection.Observability)
			if err != nil {
				t.Fatal(err)
			}
			output, err := optir.ProjectCheckedMemory(cleanup.DeadStores, function.CheckedMemory)
			if err != nil {
				t.Fatal(err)
			}
			if err := optir.VerifyDeadStoreElimination(cleanup.ScalarCFG, projection.Metadata, memorySSA, projection.Observability, liveness, cleanup.DeadStores, output.Metadata, cleanup.DeadStoreElimination); err != nil {
				t.Fatal(err)
			}
			if err := optir.VerifyCheckedMemoryProjection(cleanup.CFG, function.CheckedMemory, function.FinalMemoryProjection); err != nil {
				t.Fatal(err)
			}
			if err := optir.VerifyRegionMemorySSA(cleanup.CFG, function.FinalMemoryProjection.Metadata, function.FinalMemorySSA); err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(projection.Observability, cleanup.Projection.Observability) {
				t.Fatal("store cleanup changed live-out obligations")
			}
			if test.name == "after_pruning" {
				if len(cleanup.SCCPRewrite.SimplifiedBranches) != 1 || cleanup.DCE.EliminatedOperations == 0 {
					t.Fatal("pruning must expose a dead store and its unused arithmetic")
				}
				for _, block := range cleanup.CFG.Blocks {
					for _, operation := range block.Operations {
						if operation.Code == optir.OpIntMul || operation.Code == optir.OpCall {
							t.Fatalf("dead store producer or pruned call survived: %+v", operation)
						}
					}
				}
			}
			if test.before == test.after || test.name == "keep_effect" {
				calls, err := activeOptIRMemoryCalls(cleanup.CFG, function.CheckedMemory)
				if err != nil || len(calls) != 1 {
					t.Fatalf("reachable effect was lost: %+v, %v", calls, err)
				}
			}
		})
	}
}

func TestCheckedGlobalMemoryCleanupRejectsAlteredStoreCleanup(t *testing.T) {
	module, err := New().WithSource("cleanup_stores.oak", optIRMemoryDeadStoreCleanupProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, ok := optIRFunction(module, "after_pruning")
	if !ok {
		t.Fatalf("function not projected: %+v", module.Refusals)
	}
	for _, test := range []struct {
		name   string
		mutate func(*OptIRMemoryCleanup)
	}{
		{"scalar CFG", func(c *OptIRMemoryCleanup) { c.ScalarCFG.Name += ".stale" }},
		{"DSE CFG", func(c *OptIRMemoryCleanup) { c.DeadStores = c.ScalarCFG }},
		{"DSE report", func(c *OptIRMemoryCleanup) { c.DeadStoreElimination.Removed = nil }},
		{"producer DCE", func(c *OptIRMemoryCleanup) { c.DCE.EliminatedOperations++ }},
		{"final CFG", func(c *OptIRMemoryCleanup) { c.CFG = c.DeadStores }},
	} {
		t.Run(test.name, func(t *testing.T) {
			changed := function.MemoryCleanup
			test.mutate(&changed)
			if err := verifyOptIRMemoryCleanup(function.ForwardedLoads, function.CheckedMemory, changed); err == nil {
				t.Fatal("accepted altered store cleanup evidence")
			}
		})
	}
	if err := optir.VerifyRegionMemorySSA(function.MemoryCleanup.ScalarCFG, function.MemoryCleanup.Projection.Metadata, function.MemoryCleanup.MemorySSA); err == nil {
		t.Fatal("accepted final memory evidence for the pre-DSE CFG")
	}
}
