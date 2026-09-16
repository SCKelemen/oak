package machine

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRRV64RegionLoadsComposeWithVerifiedSpills(t *testing.T) {
	const loads = 16
	var source strings.Builder
	source.WriteString("region_spill: (): u32 = ")
	for index := 0; index < loads; index++ {
		if index != 0 {
			source.WriteString(" + ")
		}
		source.WriteString("state")
	}
	declaration := optIRRV64Declaration(t, source.String())

	cfg, metadata, memorySSA, bindings := optIRRV64RegionSpillFixture(t, loads)
	plan, _, err := planOptIRSpillsKeepingCanonicalLoopCondition(cfg, optIRRV64SpillRegisters, nil)
	if err != nil {
		t.Fatal(err)
	}
	spilledLoad := false
	for value := optir.ValueID(1); value <= loads; value++ {
		if _, spilledLoad = plan.Spills[value]; spilledLoad {
			break
		}
	}
	if !spilledLoad {
		t.Fatalf("high-pressure fixture has no spilled region load: %+v", plan.Spills)
	}

	global := bindings["checked-region"].Global
	template := &asm.Function{
		Name: "region_spill", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Globals: map[string]asm.Global{
			"state":     global,
			"unrelated": {Type: "u64", Bits: 64},
		},
	}
	lowered, err := LowerOptIRRV64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if lowered.Frame == 0 || lowered.Frame%16 != 0 {
		t.Fatalf("region-memory spill frame = %d, want nonzero alignment\n%s", lowered.Frame, body)
	}
	for _, instruction := range []string{"la t6, state", "lw t5, [t6,#0]", "sw t5, [sp,#", "lw t5, [sp,#"} {
		if !strings.Contains(body, instruction) {
			t.Fatalf("region-memory spill body lacks %q:\n%s", instruction, body)
		}
	}
	if len(lowered.Globals) != 1 || lowered.Globals["state"] != global {
		t.Fatalf("selected globals = %#v, want only state", lowered.Globals)
	}
	if !optIRRV64HasClobber(lowered, optIRRV64SpillScratchA) || !optIRRV64HasClobber(lowered, optIRRV64CopyScratch) {
		t.Fatalf("selected body does not declare spill/address scratches: %v", lowered.Clobbers)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"region_spill": true}); len(findings) != 0 {
		t.Fatalf("region-memory spill body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("region-memory spill body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func optIRRV64RegionSpillFixture(t *testing.T, loads int) (optir.CFG, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) {
	t.Helper()
	operations := make([]optir.Operation, 0, loads*2-1)
	metadata := optir.RegionMemoryMetadata{Regions: []optir.RegionID{"checked-region"}}
	for index := 0; index < loads; index++ {
		id := optir.ValueID(index + 1)
		operations = append(operations, optir.Operation{
			Code: optir.OpLoadRegion, Results: []optir.Value{{ID: id, Type: "u32"}}, Effects: []optir.Effect{optir.EffectReadMemory},
		})
		metadata.Operations = append(metadata.Operations, optir.MemoryOperationMetadata{
			Site:     optir.OperationSite{Block: 0, Index: index},
			Accesses: []optir.MemoryAccessSpec{{Region: "checked-region", Kind: optir.MemoryRead}},
		})
	}
	result := optir.ValueID(1)
	for operand := optir.ValueID(2); operand <= optir.ValueID(loads); operand++ {
		id := optir.ValueID(len(operations) + 1)
		operations = append(operations, optir.Operation{
			Code: optir.OpIntAdd, Results: []optir.Value{{ID: id, Type: "u32"}}, Operands: []optir.ValueID{result, operand},
		})
		result = id
	}
	cfg := optir.CFG{
		Name: "region_spill", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Operations: operations,
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{result}},
		}},
	}
	memorySSA := optIRAnalyzeRegionMemory(t, cfg, metadata)
	bindings := map[optir.RegionID]OptIRRegionGlobal{
		"checked-region": {Symbol: "state", Global: asm.Global{Type: "u32", Bits: 32}},
	}
	return cfg, metadata, memorySSA, bindings
}
