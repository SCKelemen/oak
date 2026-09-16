package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRArm64RegionMemoryCanonicalLoopVerifies(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
bump_state_loop: (n: u32): u32 = {
  i: u32 = u32(0)
  while i < n {
    state = state + u32(1)
    i = i + u32(1)
  }
  state
}
`)
	const region optir.RegionID = "opaque:checked-state"
	cfg := optir.CFG{
		Name: "bump_state_loop", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{
			{
				ID:         0,
				Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "n"}},
				Operations: []optir.Operation{{
					Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}},
					Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "0"}},
				}},
				Terminator: optir.Terminator{
					Kind: optir.TerminatorBranch,
					True: optir.Edge{Target: 1, Arguments: []optir.ValueID{2}},
				},
			},
			{
				ID:         1,
				Parameters: []optir.Value{{ID: 3, Type: "u32", Name: "i"}},
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
				Terminator: optir.Terminator{
					Kind: optir.TerminatorBranch,
					True: optir.Edge{Target: 1, Arguments: []optir.ValueID{8}},
				},
			},
			{
				ID: 3,
				Operations: []optir.Operation{{
					Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 9, Type: "u32"}},
					Effects: []optir.Effect{optir.EffectReadMemory},
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
		t.Fatalf("canonical-loop MemorySSA evidence does not verify: %v", err)
	}

	accesses := make(map[optir.OperationSite]optir.MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accesses[access.Site] = access
	}
	bodyLoad := accesses[optir.OperationSite{Block: 2, Index: 0}]
	bodyStore := accesses[optir.OperationSite{Block: 2, Index: 3}]
	exitLoad := accesses[optir.OperationSite{Block: 3, Index: 0}]
	var entryVersion, headerPhi *optir.MemoryVersion
	for index := range memorySSA.Versions {
		version := &memorySSA.Versions[index]
		if version.Region == region && version.Kind == optir.MemoryVersionEntry && version.Block == 0 {
			entryVersion = version
		}
		if version.Region == region && version.Kind == optir.MemoryVersionPhi && version.Block == 1 {
			headerPhi = version
		}
	}
	if entryVersion == nil {
		t.Fatalf("canonical loop has no entry memory version: %+v", memorySSA.Versions)
	}
	if headerPhi == nil {
		t.Fatalf("canonical loop has no header memory phi: %+v", memorySSA.Versions)
	}
	wantIncoming := []optir.MemoryIncoming{
		{Predecessor: 0, Version: entryVersion.ID},
		{Predecessor: 2, Version: bodyStore.Output},
	}
	if !reflect.DeepEqual(headerPhi.Incoming, wantIncoming) ||
		bodyLoad.Input != headerPhi.ID || bodyStore.Input != headerPhi.ID || exitLoad.Input != headerPhi.ID {
		t.Fatalf("loop memory flow = phi %+v, body load %+v, body store %+v, exit load %+v; want incoming %+v", *headerPhi, bodyLoad, bodyStore, exitLoad, wantIncoming)
	}

	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "bump_state_loop", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "n"}},
		Globals: map[string]asm.Global{
			"state":     global,
			"unrelated": {Type: "u64", Bits: 64},
		},
	}
	lowered, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, map[optir.RegionID]OptIRRegionGlobal{
		region: {Symbol: "state", Global: global},
	})
	if err != nil {
		t.Fatal(err)
	}
	body := text(lowered.Items)
	if strings.Count(body, "adrp x17, state") != 3 || !strings.Contains(body, "ldr ") || !strings.Contains(body, "str ") ||
		!strings.Contains(body, "cbz ") || !strings.Contains(body, "b optir_b1") {
		t.Fatalf("selected body does not retain the canonical global-memory loop:\n%s", body)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"bump_state_loop": true}); len(findings) != 0 {
		t.Fatalf("selected canonical loop fails seam check: %v\n%s", findings, body)
	}
	verdict := asm.Verify(lowered, declaration, declaration.Body)
	if verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected canonical-loop verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
	if !strings.Contains(verdict.Message, "package state it writes (state)") {
		t.Fatalf("proven canonical-loop verdict does not cover package state: %s", verdict.Message)
	}
}
