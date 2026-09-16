package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

const optIRMemoryCleanupProgram = `
state: u32 = u32(0)
side: u32 = u32(0)
ghost: u32 = u32(0)
tiny: u8 = u8(0)

poison: (value: u32): u32 {
  ghost = value
  value
}

fold_memory: (value: u32): u32 {
  state = u32(20)
  answer: u32 = state + u32(22)
  state == u32(20) ? {
    side = answer
    answer
  } | poison(value)
}

same_value: (flag: Bool, value: u32): u32 {
  flag ? { state = value } | { state = value }
  state + value
}

memory_free: (): u32 = false ? poison(u32(1)) | u32(42)

wrap_memory: (): u8 {
  tiny = u8(255)
  tiny + u8(43)
}

main: (): i32 = fold_memory(u32(99)) == u32(42) && side == u32(42) && wrap_memory() == u8(42) ? i32(42) | i32(1)
`

func TestCheckedGlobalMemoryCleanupFoldsAndPrunesAfterForwarding(t *testing.T) {
	module, err := New().WithSource("memory_cleanup.oak", optIRMemoryCleanupProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	fold, ok := optIRFunction(module, "fold_memory")
	if !ok {
		t.Fatalf("fold_memory not projected: %+v", module.Refusals)
	}
	cleanup := fold.MemoryCleanup
	if len(fold.RegionLoadForwarding.Replacements) != 2 || len(cleanup.SCCPRewrite.SimplifiedBranches) != 1 || len(cleanup.SCCPRewrite.RewrittenValues) == 0 || cleanup.Simplification.Changes() == 0 {
		t.Fatalf("expected forwarding to enable branch/arithmetic/scalar cleanup: forwarding %+v, cleanup %+v", fold.RegionLoadForwarding, cleanup)
	}
	if calls, err := activeOptIRMemoryCalls(fold.ForwardedLoads, fold.CheckedMemory); err != nil || len(calls) != 1 {
		t.Fatalf("expected one call before scalar cleanup: %+v, %v", calls, err)
	}
	if calls, err := activeOptIRMemoryCalls(cleanup.CFG, fold.CheckedMemory); err != nil || len(calls) != 0 {
		t.Fatalf("unreachable call remains after cleanup: %+v, %v", calls, err)
	}
	if len(cleanup.CFG.Blocks) != 1 || len(cleanup.Projection.Metadata.Regions) != 2 || len(fold.ForwardedLoadMetadata.Regions) != 3 {
		t.Fatalf("unreachable control/region was not removed: CFG %+v, metadata %+v", cleanup.CFG, cleanup.Projection.Metadata)
	}
	if stores, loads := countOptIRMemoryOperations(cleanup.CFG); stores != 2 || loads != 0 {
		t.Fatalf("cleanup changed surviving effects: stores=%d loads=%d", stores, loads)
	}
	block := cleanup.CFG.Blocks[0]
	constantReturn := false
	for _, operation := range block.Operations {
		if operation.Code == optir.OpIntAdd || operation.Code == optir.OpEqual {
			t.Fatalf("newly constant arithmetic/comparison remains: %+v", operation)
		}
		if operation.Code == optir.OpConstInt && len(operation.Results) == 1 && operation.Results[0].ID == block.Terminator.Values[0] {
			for _, attribute := range operation.Attributes {
				constantReturn = constantReturn || attribute.Name == optir.AttributeValue && attribute.Value == "42"
			}
		}
	}
	if !constantReturn {
		t.Fatalf("folded function does not return constant 42: %+v", block)
	}
	if err := verifyOptIRMemoryCleanup(fold.ForwardedLoads, fold.CheckedMemory, cleanup); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyCFGCheckedFacts(cleanup.CFG, fold.CheckedFacts); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyCheckedMemoryProjection(cleanup.CFG, fold.CheckedMemory, fold.FinalMemoryProjection); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionMemorySSA(cleanup.CFG, fold.FinalMemoryProjection.Metadata, fold.FinalMemorySSA); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyCheckedMemoryProjection(fold.ForwardedLoads, fold.CheckedMemory, fold.FinalMemoryProjection); err == nil {
		t.Fatal("final projection was accepted against pre-cleanup CFG")
	}
	congruent, ok := optIRFunction(module, "same_value")
	if !ok || congruent.MemoryCleanup.Simplification.BlockParameters.EliminatedParameters == 0 {
		t.Fatalf("memory promotion did not enable phi cleanup: %+v", congruent.MemoryCleanup)
	}
	pure, ok := optIRFunction(module, "memory_free")
	if !ok || !pure.CheckedMemory.HasMemoryEffects() || len(pure.MemoryCleanup.Projection.Metadata.Regions) != 0 || len(pure.MemoryCleanup.CFG.Blocks) == 0 {
		t.Fatalf("removed memory path did not retain a scalar final CFG: %+v", pure.MemoryCleanup)
	}
	wrapped, ok := optIRFunction(module, "wrap_memory")
	if !ok || wrapped.MemoryCleanup.Changes() == 0 {
		t.Fatal("narrow memory arithmetic was not cleaned")
	}
	wrappedBlock := wrapped.MemoryCleanup.CFG.Blocks[0]
	wrappedConstant := false
	for _, operation := range wrappedBlock.Operations {
		if operation.Code == optir.OpConstInt && operation.Results[0].ID == wrappedBlock.Terminator.Values[0] && operation.Results[0].Type == "u8" {
			for _, attribute := range operation.Attributes {
				wrappedConstant = wrappedConstant || attribute.Name == optir.AttributeValue && attribute.Value == "42"
			}
		}
	}
	if !wrappedConstant {
		t.Fatalf("u8 memory-derived arithmetic did not wrap to 42: %+v", wrappedBlock)
	}
}

func TestCheckedGlobalMemoryCleanupRejectsStaleAndForgedEvidence(t *testing.T) {
	module, err := New().WithSource("memory_cleanup.oak", optIRMemoryCleanupProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	fold, ok := optIRFunction(module, "fold_memory")
	if !ok {
		t.Fatalf("fold_memory not projected: %+v", module.Refusals)
	}
	for _, test := range []struct {
		name   string
		mutate func(*OptIRMemoryCleanup)
	}{
		{"CFG", func(cleanup *OptIRMemoryCleanup) { cleanup.CFG.Name += ".stale" }},
		{"SCCP report", func(cleanup *OptIRMemoryCleanup) { cleanup.SCCPRewrite.SimplifiedBranches = nil }},
		{"GVN/DCE report", func(cleanup *OptIRMemoryCleanup) { cleanup.Simplification.DCE.EliminatedOperations++ }},
		{"projection", func(cleanup *OptIRMemoryCleanup) { cleanup.Projection = optir.CheckedMemoryProjection{} }},
		{"MemorySSA", func(cleanup *OptIRMemoryCleanup) { cleanup.MemorySSA = optir.RegionMemorySSA{} }},
	} {
		t.Run(test.name, func(t *testing.T) {
			changed := fold.MemoryCleanup
			test.mutate(&changed)
			if err := verifyOptIRMemoryCleanup(fold.ForwardedLoads, fold.CheckedMemory, changed); err == nil {
				t.Fatal("accepted altered cleanup artifact")
			}
		})
	}
	if err := verifyOptIRMemoryCleanup(fold.ForwardedLoads, optir.CheckedMemoryAuthority{}, fold.MemoryCleanup); err == nil {
		t.Fatal("accepted cleanup with missing authority")
	}
	before := fold.ForwardedLoads
	before.Blocks = append([]optir.Block(nil), before.Blocks...)
	for index := range before.Blocks {
		block := &before.Blocks[index]
		block.Operations = append([]optir.Operation(nil), block.Operations...)
		for i := range block.Operations {
			if block.Operations[i].Code == optir.OpCall {
				block.Operations[i].MemoryCallID = "forged-call"
			}
		}
	}
	if _, err := cleanupOptIRMemory(before, fold.CheckedMemory); err == nil {
		t.Fatal("cleanup hid unauthenticated input by deleting the unreachable call")
	}
	again, err := cleanupOptIRMemory(fold.ForwardedLoads, fold.CheckedMemory)
	if err != nil || !reflect.DeepEqual(again, fold.MemoryCleanup) {
		t.Fatalf("cleanup is not deterministic: %v", err)
	}
}
