package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRRV64RegionMemoryDiamondVerifies(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
choose_store: (flag: Bool, left: u32, right: u32): u32 = {
  flag ? { state = left } | { state = right }
  state
}
`)
	cfg := optir.CFG{
		Name: "choose_store", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{
			{
				ID: 0,
				Parameters: []optir.Value{
					{ID: 1, Type: optir.TypeBool, Name: "flag"},
					{ID: 2, Type: "u32", Name: "left"},
					{ID: 3, Type: "u32", Name: "right"},
				},
				Terminator: optir.Terminator{
					Kind: optir.TerminatorCondBranch, Condition: 1,
					True: optir.Edge{Target: 1}, False: optir.Edge{Target: 2},
				},
			},
			{
				ID: 1,
				Operations: []optir.Operation{{
					Code: optir.OpStoreRegion, Operands: []optir.ValueID{2}, Effects: []optir.Effect{optir.EffectWriteMemory},
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3}},
			},
			{
				ID: 2,
				Operations: []optir.Operation{{
					Code: optir.OpStoreRegion, Operands: []optir.ValueID{3}, Effects: []optir.Effect{optir.EffectWriteMemory},
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3}},
			},
			{
				ID: 3,
				Operations: []optir.Operation{{
					Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 4, Type: "u32"}}, Effects: []optir.Effect{optir.EffectReadMemory},
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{4}},
			},
		},
	}
	const region optir.RegionID = "checked-state"
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{region},
		Operations: []optir.MemoryOperationMetadata{
			{Site: optir.OperationSite{Block: 1, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryWrite, WholeRegion: true}}},
			{Site: optir.OperationSite{Block: 2, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryWrite, WholeRegion: true}}},
			{Site: optir.OperationSite{Block: 3, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryRead}}},
		},
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "choose_store", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{
			{Register: optIRRV64Register(10), Param: "flag"},
			{Register: optIRRV64Register(11), Param: "left"},
			{Register: optIRRV64Register(12), Param: "right"},
		},
		Globals: map[string]asm.Global{
			"state":  global,
			"unused": {Type: "u64", Bits: 64},
		},
	}
	lowered, err := LowerOptIRRV64WithRegionMemory(cfg, template, metadata, memorySSA, map[optir.RegionID]OptIRRegionGlobal{
		region: {Symbol: "state", Global: global},
	})
	if err != nil {
		t.Fatal(err)
	}
	if want := map[string]asm.Global{"state": global}; !reflect.DeepEqual(lowered.Globals, want) {
		t.Fatalf("selected globals = %#v, want %#v", lowered.Globals, want)
	}
	body := text(lowered.Items)
	if strings.Count(body, "sw ") != 2 || strings.Count(body, "lw ") != 1 {
		t.Fatalf("selected body does not contain two arm stores and one merge load:\n%s", body)
	}
	if strings.Count(body, "la t6, state") != 3 || !strings.Contains(body, "beqz a0, optir_b2") {
		t.Fatalf("selected body does not retain the region-memory diamond:\n%s", body)
	}
	if !optIRRV64HasClobber(lowered, optIRRV64CopyScratch) {
		t.Fatalf("selected body does not declare address scratch t6: %v", lowered.Clobbers)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"choose_store": true}); len(findings) != 0 {
		t.Fatalf("selected body fails seam check: %v\n%s", findings, body)
	}
	verdict := asm.Verify(lowered, declaration, declaration.Body)
	if verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
	if !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("proven verdict does not cover package state: %s", verdict.Message)
	}
}
