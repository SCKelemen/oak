package compiler

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

const optIRMemoryLICMProgram = `
cap: u32 = u32(0)

sum_cap: (n: u32): u32 {
  i: u32 = u32(0)
  total: u32 = u32(0)
  while i < n {
    total = total + cap * u32(3)
    i = i + u32(1)
  }
  total
}

keep_variant: (n: u32): u32 {
  i: u32 = u32(0)
  total: u32 = u32(0)
  while i < n {
    cap = cap + u32(1)
    total = total + cap * u32(3)
    i = i + u32(1)
  }
  total
}

main: (): i32 {
  cap = u32(7)
  first: Bool = sum_cap(u32(0)) == u32(0) && sum_cap(u32(1)) == u32(21) && sum_cap(u32(2)) == u32(42)
  cap = u32(5)
  second: Bool = sum_cap(u32(3)) == u32(45)
  cap = u32(2147483648)
  wrapped: Bool = sum_cap(u32(2)) == u32(0)
  cap = u32(0)
  variant: Bool = keep_variant(u32(3)) == u32(18) && cap == u32(3)
  first && second && wrapped && variant ? i32(42) | i32(1)
}
`

func TestCheckedGlobalMemoryCleanupHoistsNewlyInvariantArithmetic(t *testing.T) {
	module, err := New().WithSource("memory_licm.oak", optIRMemoryLICMProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, ok := optIRFunction(module, "sum_cap")
	if !ok {
		t.Fatalf("sum_cap not projected: %+v", module.Refusals)
	}
	if len(function.RegionLoadForwarding.Insertions) != 1 || function.MemoryCleanup.Simplification.BlockParameters.EliminatedParameters == 0 {
		t.Fatalf("fixture must expose invariance through memory promotion and phi cleanup: %+v, %+v", function.RegionLoadForwarding, function.MemoryCleanup.Simplification)
	}
	cfg := function.MemoryCleanup.CFG
	loops, err := optir.AnalyzeLoops(cfg)
	if err != nil || len(loops.Loops) != 1 || !loops.Loops[0].HasPreheader {
		t.Fatalf("expected one canonical final loop: %+v, %v", loops, err)
	}
	multiplies := 0
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if operation.Code == optir.OpIntMul {
				multiplies++
				if block.ID != loops.Loops[0].Preheader {
					t.Fatalf("memory-derived invariant multiplication remains in block %d instead of preheader %d", block.ID, loops.Loops[0].Preheader)
				}
			}
		}
	}
	if multiplies != 1 {
		t.Fatalf("expected one retained multiplication, got %d", multiplies)
	}
	cleanup := function.MemoryCleanup
	if cleanup.LoopMotion.HoistedOperations != 1 || len(cleanup.LoopMotion.Moves) != 1 || cleanup.LoopMotion.Moves[0].Code != optir.OpIntMul {
		t.Fatalf("expected precisely the newly invariant multiplication to move: %+v", cleanup.LoopMotion)
	}
	before, err := optir.AnalyzeLoops(cleanup.DCECleaned)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(before.BackEdges, loops.BackEdges) || !reflect.DeepEqual(before.Dominators, loops.Dominators) {
		t.Fatal("pure motion changed loop topology")
	}
	for _, snapshot := range []optir.CFG{cleanup.DCECleaned, cleanup.CFG} {
		if err := optir.VerifyCFGCheckedFacts(snapshot, function.CheckedFacts); err != nil {
			t.Fatal(err)
		}
	}
	if err := optir.VerifyCheckedMemoryProjection(cleanup.CFG, function.CheckedMemory, function.FinalMemoryProjection); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionMemorySSA(cleanup.CFG, function.FinalMemoryProjection.Metadata, function.FinalMemorySSA); err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyCheckedMemoryProjection(cleanup.DCECleaned, function.CheckedMemory, function.FinalMemoryProjection); err == nil {
		t.Fatal("final projection was accepted against the pre-motion snapshot")
	}
	stale, err := optir.AnalyzeLoops(function.ForwardedLoads)
	if err != nil {
		t.Fatal(err)
	}
	if _, _, err := optir.HoistLoopInvariantsWithAnalysis(cleanup.DCECleaned, stale); err == nil {
		t.Fatal("pre-cleanup loop evidence was accepted for final LICM")
	}
	if err := verifyOptIRMemoryCleanup(function.ForwardedLoads, function.CheckedMemory, cleanup); err != nil {
		t.Fatal(err)
	}
}

func TestCheckedGlobalMemoryCleanupKeepsVariantAndTrappingArithmetic(t *testing.T) {
	module, err := New().WithSource("memory_licm.oak", optIRMemoryLICMProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	variant, ok := optIRFunction(module, "keep_variant")
	if !ok {
		t.Fatalf("keep_variant not projected: %+v", module.Refusals)
	}
	if variant.MemoryCleanup.LoopMotion.HoistedOperations != 0 {
		t.Fatalf("loop-carried memory arithmetic was hoisted: %+v", variant.MemoryCleanup.LoopMotion)
	}
	assertMemoryCleanupOperationInLoop(t, variant.MemoryCleanup.CFG, optir.OpIntMul)
	invariant, ok := optIRFunction(module, "sum_cap")
	if !ok {
		t.Fatal("missing sum_cap")
	}
	// Exercise the transform's closed vocabulary with a potentially trapping
	// division of the newly invariant value. No source or memory authority is
	// synthesized, and this synthetic arithmetic CFG is never emitted.
	input := invariant.ForwardedLoads
	input.Blocks = append([]optir.Block(nil), input.Blocks...)
	var divisor optir.ValueID
	for _, block := range input.Blocks {
		if block.ID == input.Entry && len(block.Parameters) == 1 {
			divisor = block.Parameters[0].ID
		}
	}
	if divisor == 0 {
		t.Fatal("missing n parameter for zero-trip division fixture")
	}
	changed := false
	for index := range input.Blocks {
		block := &input.Blocks[index]
		block.Operations = append([]optir.Operation(nil), block.Operations...)
		for i := range block.Operations {
			if block.Operations[i].Code == optir.OpIntMul {
				block.Operations[i].Code = optir.OpIntDiv
				// n=0 skips the body; moving cap/n out would introduce a trap.
				block.Operations[i].Operands = []optir.ValueID{block.Operations[i].Operands[0], divisor}
				block.Operations[i].Effects = []optir.Effect{optir.EffectTrap}
				changed = true
			}
		}
	}
	if !changed {
		t.Fatal("fixture has no multiplication to replace")
	}
	cleanup, err := cleanupOptIRMemory(input, invariant.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	if cleanup.LoopMotion.HoistedOperations != 0 {
		t.Fatalf("potentially trapping arithmetic was hoisted: %+v", cleanup.LoopMotion)
	}
	assertMemoryCleanupOperationInLoop(t, cleanup.CFG, optir.OpIntDiv)
}

func assertMemoryCleanupOperationInLoop(t *testing.T, cfg optir.CFG, code string) {
	t.Helper()
	loops, err := optir.AnalyzeLoops(cfg)
	if err != nil || len(loops.Loops) != 1 {
		t.Fatalf("expected one loop: %+v, %v", loops, err)
	}
	members := map[optir.BlockID]bool{}
	for _, block := range loops.Loops[0].Blocks {
		members[block] = true
	}
	count := 0
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if operation.Code == code {
				count++
				if !members[block.ID] {
					t.Fatalf("%s escaped the loop into block %d", code, block.ID)
				}
			}
		}
	}
	if count != 1 {
		t.Fatalf("expected one %s in the loop, found %d", code, count)
	}
}

func TestCheckedGlobalMemoryCleanupRejectsAlteredLoopMotion(t *testing.T) {
	module, err := New().WithSource("memory_licm.oak", optIRMemoryLICMProgram).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, ok := optIRFunction(module, "sum_cap")
	if !ok {
		t.Fatalf("sum_cap not projected: %+v", module.Refusals)
	}
	for _, test := range []struct {
		name   string
		mutate func(*OptIRMemoryCleanup)
	}{
		{"pre-LICM CFG", func(c *OptIRMemoryCleanup) { c.DCECleaned = c.CFG }},
		{"final CFG", func(c *OptIRMemoryCleanup) { c.CFG = c.DCECleaned }},
		{"move count", func(c *OptIRMemoryCleanup) { c.LoopMotion.HoistedOperations++ }},
		{"moves", func(c *OptIRMemoryCleanup) { c.LoopMotion.Moves = nil }},
		{"loop count", func(c *OptIRMemoryCleanup) { c.LoopMotion.LoopsAnalyzed++ }},
	} {
		t.Run(test.name, func(t *testing.T) {
			changed := function.MemoryCleanup
			test.mutate(&changed)
			if err := verifyOptIRMemoryCleanup(function.ForwardedLoads, function.CheckedMemory, changed); err == nil {
				t.Fatal("accepted altered loop-motion evidence")
			}
		})
	}
}
