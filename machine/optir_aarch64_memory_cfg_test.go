package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRArm64RegionMemoryDiamondVerifies(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
choose_store: (flag: Bool, left: u32, right: u32): u32 = {
  flag ? { state = left } | { state = right }
  state
}
`)
	const region optir.RegionID = "opaque:checked-state"
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
	if err := optir.VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		t.Fatalf("diamond MemorySSA evidence does not verify: %v", err)
	}

	accesses := make(map[optir.OperationSite]optir.MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accesses[access.Site] = access
	}
	leftStore := accesses[optir.OperationSite{Block: 1, Index: 0}]
	rightStore := accesses[optir.OperationSite{Block: 2, Index: 0}]
	mergeLoad := accesses[optir.OperationSite{Block: 3, Index: 0}]
	var mergePhi *optir.MemoryVersion
	for index := range memorySSA.Versions {
		version := &memorySSA.Versions[index]
		if version.Region == region && version.Kind == optir.MemoryVersionPhi && version.Block == 3 {
			mergePhi = version
			break
		}
	}
	if mergePhi == nil {
		t.Fatalf("diamond has no merge memory phi: %+v", memorySSA.Versions)
	}
	wantIncoming := []optir.MemoryIncoming{
		{Predecessor: 1, Version: leftStore.Output},
		{Predecessor: 2, Version: rightStore.Output},
	}
	if !reflect.DeepEqual(mergePhi.Incoming, wantIncoming) || mergeLoad.Input != mergePhi.ID {
		t.Fatalf("merge memory flow = phi %+v, load %+v; want incoming %+v", *mergePhi, mergeLoad, wantIncoming)
	}

	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: "choose_store", Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{
			{Register: w(0), Param: "flag"},
			{Register: w(1), Param: "left"},
			{Register: w(2), Param: "right"},
		},
		Globals: map[string]asm.Global{
			"state":     global,
			"unrelated": {Type: "u64", Bits: 64},
		},
	}
	bindings := map[optir.RegionID]OptIRRegionGlobal{
		region: {Symbol: "state", Global: global},
	}
	lowered, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
	if err != nil {
		t.Fatal(err)
	}
	if want := map[string]asm.Global{"state": global}; !reflect.DeepEqual(lowered.Globals, want) {
		t.Fatalf("selected globals = %#v, want %#v", lowered.Globals, want)
	}

	body := text(lowered.Items)
	for _, instruction := range []string{
		"str w1, [x17,#0]",
		"str w2, [x17,#0]",
		"ldr w0, [x17,#0]",
	} {
		if !strings.Contains(body, instruction) {
			t.Fatalf("selected diamond lacks %q:\n%s", instruction, body)
		}
	}
	conditionalBranches, blockLabels, lowAddressAdds := 0, 0, 0
	for _, item := range lowered.Items {
		switch item := item.(type) {
		case asm.Instruction:
			if item.Mnemonic == "cbz" || item.Mnemonic == "cbnz" {
				conditionalBranches++
			}
			if item.Mnemonic == "add" && len(item.Operands) == 3 {
				symbol, ok := item.Operands[2].(asm.Symbol)
				if ok && symbol.Name == "state" && symbol.Lo12 {
					lowAddressAdds++
				}
			}
		case asm.Label:
			if strings.HasPrefix(item.Name, "optir_b") {
				blockLabels++
			}
		}
	}
	if strings.Count(body, "adrp x17, state") != 3 || lowAddressAdds != 3 {
		t.Fatalf("selected diamond does not address the authorized global exactly once per access:\n%s", body)
	}
	if conditionalBranches != 1 || blockLabels != 4 {
		t.Fatalf("selected diamond has %d conditional branches and %d block labels:\n%s", conditionalBranches, blockLabels, body)
	}
	hasAddressScratch := false
	for _, clobber := range lowered.Clobbers {
		hasAddressScratch = hasAddressScratch || clobber.Num == optIRCopyScratch
	}
	if !hasAddressScratch {
		t.Fatalf("selected diamond omits address scratch x17 from clobbers: %v", lowered.Clobbers)
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{"choose_store": true}); len(findings) != 0 {
		t.Fatalf("selected diamond fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("selected diamond verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}
