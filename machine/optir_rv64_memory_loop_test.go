package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRRV64RegionMemoryCanonicalLoopVerifies(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
loop_store: (n: u32): u32 = {
  i: u32 = 0
  while i < n {
    state = state + u32(1)
    i = i + u32(1)
  }
  state
}
`)
	const region optir.RegionID = "opaque:checked-state"
	cfg := optir.CFG{
		Name: "loop_store", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{
			{
				ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "n"}},
				Operations: []optir.Operation{{
					Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}},
					Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}},
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1, Arguments: []optir.ValueID{2}}},
			},
			{
				ID: 1, Parameters: []optir.Value{{ID: 3, Type: "u32", Name: "i"}},
				Operations: []optir.Operation{{
					Code: optir.OpLess, Results: []optir.Value{{ID: 4, Type: optir.TypeBool}}, Operands: []optir.ValueID{3, 1},
				}},
				Terminator: optir.Terminator{
					Kind: optir.TerminatorCondBranch, Condition: 4,
					True: optir.Edge{Target: 2}, False: optir.Edge{Target: 3},
				},
			},
			{
				ID: 2,
				Operations: []optir.Operation{
					{
						Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 5, Type: "u32"}},
						Effects: []optir.Effect{optir.EffectReadMemory},
					},
					{
						Code: optir.OpConstInt, Results: []optir.Value{{ID: 6, Type: "u32"}},
						Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}},
					},
					{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 7, Type: "u32"}}, Operands: []optir.ValueID{5, 6}},
					{Code: optir.OpStoreRegion, Operands: []optir.ValueID{7}, Effects: []optir.Effect{optir.EffectWriteMemory}},
					{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 8, Type: "u32"}}, Operands: []optir.ValueID{3, 6}},
				},
				Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1, Arguments: []optir.ValueID{8}}},
			},
			{
				ID: 3,
				Operations: []optir.Operation{{
					Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 9, Type: "u32"}}, Effects: []optir.Effect{optir.EffectReadMemory},
				}},
				Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{9}},
			},
		},
	}
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{region},
		Operations: []optir.MemoryOperationMetadata{
			{Site: optir.OperationSite{Block: 2, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryRead}}},
			{Site: optir.OperationSite{Block: 2, Index: 3}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryWrite, WholeRegion: true}}},
			{Site: optir.OperationSite{Block: 3, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryRead}}},
		},
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		t.Fatalf("loop MemorySSA evidence does not verify: %v", err)
	}

	accesses := make(map[optir.OperationSite]optir.MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accesses[access.Site] = access
	}
	bodyLoad := accesses[optir.OperationSite{Block: 2, Index: 0}]
	store := accesses[optir.OperationSite{Block: 2, Index: 3}]
	exitLoad := accesses[optir.OperationSite{Block: 3, Index: 0}]
	var entry, headerPhi *optir.MemoryVersion
	for index := range memorySSA.Versions {
		version := &memorySSA.Versions[index]
		if version.Region != region {
			continue
		}
		switch {
		case version.Kind == optir.MemoryVersionEntry:
			entry = version
		case version.Kind == optir.MemoryVersionPhi && version.Block == 1:
			headerPhi = version
		}
	}
	if entry == nil || headerPhi == nil {
		t.Fatalf("loop lacks entry/header memory versions: %+v", memorySSA.Versions)
	}
	wantIncoming := []optir.MemoryIncoming{
		{Predecessor: 0, Version: entry.ID},
		{Predecessor: 2, Version: store.Output},
	}
	if !reflect.DeepEqual(headerPhi.Incoming, wantIncoming) {
		t.Fatalf("loop memory phi = %+v, want incoming %+v", *headerPhi, wantIncoming)
	}
	if bodyLoad.Input != headerPhi.ID || store.Input != headerPhi.ID || store.Output == 0 || exitLoad.Input != headerPhi.ID {
		t.Fatalf("loop memory flow = body load %+v, store %+v, exit load %+v, header phi %+v", bodyLoad, store, exitLoad, *headerPhi)
	}

	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "loop_store", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "n"}},
		Globals: map[string]asm.Global{
			"state":     global,
			"unrelated": {Type: "u64", Bits: 64},
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
	if lowered.Frame != 0 {
		t.Fatalf("low-pressure loop unexpectedly spills to a %d-byte frame", lowered.Frame)
	}
	body := text(lowered.Items)
	if strings.Count(body, "la t6, state") != 3 || strings.Count(body, "sw ") != 1 || strings.Count(body, "lw ") != 2 {
		t.Fatalf("selected loop does not contain one body load/store and one exit load:\n%s", body)
	}
	if !strings.Contains(body, "j optir_b1") || !strings.Contains(body, "beqz ") {
		t.Fatalf("selected loop does not retain the conditional header and backedge:\n%s", body)
	}
	if !optIRRV64HasClobber(lowered, optIRRV64CopyScratch) {
		t.Fatalf("selected loop does not declare address scratch t6: %v", lowered.Clobbers)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"loop_store": true}); len(findings) != 0 {
		t.Fatalf("selected loop fails seam check: %v\n%s", findings, body)
	}
	verdict := asm.Verify(lowered, declaration, declaration.Body)
	if verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected loop verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
	if !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("proven verdict does not cover package state: %s", verdict.Message)
	}
}
