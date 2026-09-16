package machine

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRArm64RegionMemoryComposesWithVerifiedSpills(t *testing.T) {
	const (
		name   = "memory_spill_a64"
		values = 20
		region = optir.RegionID("opaque:state")
	)
	declaration := optIRRV64Declaration(t, optIRArm64MemorySpillSource(name, values))
	cfg, load, stored := optIRArm64MemorySpillCFG(name, values)
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{region},
		Operations: []optir.MemoryOperationMetadata{
			{Site: optir.OperationSite{Block: 0, Index: 0}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryRead}}},
			{Site: optir.OperationSite{Block: 0, Index: len(cfg.Blocks[0].Operations) - 1}, Accesses: []optir.MemoryAccessSpec{{Region: region, Kind: optir.MemoryWrite, WholeRegion: true}}},
		},
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := optir.VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		t.Fatalf("pressure fixture MemorySSA evidence does not verify: %v", err)
	}

	fixed := map[optir.ValueID]int{1: 0}
	if _, err := optir.ColorRegisters(cfg, optIRArm64Registers, fixed); err == nil {
		t.Fatal("memory pressure fixture did not exceed the strict register pool")
	}
	allocation, err := optIRArm64Allocate(cfg, optIRTypes(cfg), fixed)
	if err != nil {
		t.Fatal(err)
	}
	if allocation.frame == 0 {
		t.Fatalf("memory pressure fixture did not materialize a spill frame: %+v", allocation.spills)
	}
	loadSlot, loadSpilled := allocation.spills[load]
	storeRegister, storeColored := allocation.colors[stored]
	if !loadSpilled || !storeColored {
		t.Fatalf("fixture lacks a spilled region load and colored store operand: load=%d/%t store=x%d/%t spills=%+v", loadSlot, loadSpilled, storeRegister, storeColored, allocation.spills)
	}
	if _, rematerialized := allocation.rematerializations[load]; rematerialized {
		t.Fatalf("effectful region load %d was incorrectly rematerialized", load)
	}
	loadFrame, materialized := allocation.slots[loadSlot]
	if !materialized {
		t.Fatalf("region-load spill slot %d has no physical frame location", loadSlot)
	}

	global := asm.Global{Type: "u32", Bits: 32}
	template := &asm.Function{
		Name: name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
		Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
		Globals:  map[string]asm.Global{"state": global},
	}
	lowered, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, map[optir.RegionID]OptIRRegionGlobal{
		region: {Symbol: "state", Global: global},
	})
	if err != nil {
		t.Fatal(err)
	}
	if lowered.Frame == 0 || lowered.Frame%16 != 0 || lowered.Frame > optIRArm64MaxSpillFrame {
		t.Fatalf("materialized memory/spill frame = %d", lowered.Frame)
	}
	body := text(lowered.Items)
	for _, instruction := range []string{
		"ldr w17, [x17,#0]",
		fmt.Sprintf("str w17, [sp,#%d]", loadFrame.offset),
		fmt.Sprintf("ldr w16, [sp,#%d]", loadFrame.offset),
		fmt.Sprintf("str w%d, [x17,#0]", storeRegister),
	} {
		if !strings.Contains(body, instruction) {
			t.Fatalf("memory/spill body lacks %q:\n%s", instruction, body)
		}
	}
	if findings := asm.Check(lowered, declaration, map[string]bool{name: true}); len(findings) != 0 {
		t.Fatalf("memory/spill body fails seam check: %v\n%s", findings, body)
	}
	if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
		t.Fatalf("memory/spill body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
	}
}

func optIRArm64MemorySpillCFG(name string, values int) (optir.CFG, optir.ValueID, optir.ValueID) {
	cfg := optIRTypedPressureCFG(name, "u32", values)
	block := &cfg.Blocks[0]
	load := optir.ValueID(3*values + 1)
	result := load + 1
	loadOperation := optir.Operation{
		Code: optir.OpLoadRegion, Results: []optir.Value{{ID: load, Type: "u32"}}, Effects: []optir.Effect{optir.EffectReadMemory},
	}
	block.Operations = append([]optir.Operation{loadOperation}, block.Operations...)
	block.Operations = append(block.Operations,
		optir.Operation{Code: optir.OpIntAdd, Results: []optir.Value{{ID: result, Type: "u32"}}, Operands: []optir.ValueID{block.Terminator.Values[0], load}},
		optir.Operation{Code: optir.OpStoreRegion, Operands: []optir.ValueID{3}, Effects: []optir.Effect{optir.EffectWriteMemory}},
	)
	block.Terminator.Values[0] = result
	return cfg, load, 3
}

func optIRArm64MemorySpillSource(name string, values int) string {
	var source strings.Builder
	fmt.Fprintf(&source, "%s: (x: u32): u32 = {\n  seed: u32 = state\n", name)
	for index := 1; index <= values; index++ {
		fmt.Fprintf(&source, "  v%d: u32 = x + u32(%d)\n", index, index)
	}
	source.WriteString("  total: u32 = ")
	for index := 1; index <= values; index++ {
		if index > 1 {
			source.WriteString(" + ")
		}
		fmt.Fprintf(&source, "v%d", index)
	}
	source.WriteString(" + seed\n  state = v1\n  total\n}\n")
	return source.String()
}
