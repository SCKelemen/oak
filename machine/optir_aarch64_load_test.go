package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRArm64RegionLoadsVerifyForEveryScalarWidth(t *testing.T) {
	tests := []struct {
		typ  optir.Type
		load string
	}{
		{typ: optir.TypeBool, load: "ldr w0, [x17,#0]"},
		{typ: "u8", load: "ldrb w0, [x17,#0]"},
		{typ: "i8", load: "ldrsb w0, [x17,#0]"},
		{typ: "u16", load: "ldrh w0, [x17,#0]"},
		{typ: "i16", load: "ldrsh w0, [x17,#0]"},
		{typ: "u32", load: "ldr w0, [x17,#0]"},
		{typ: "i32", load: "ldr w0, [x17,#0]"},
		{typ: "u64", load: "ldr x0, [x17,#0]"},
		{typ: "i64", load: "ldr x0, [x17,#0]"},
	}
	for _, test := range tests {
		t.Run(string(test.typ), func(t *testing.T) {
			name := "read_region_" + strings.ToLower(string(test.typ))
			declaration := optIRRV64Declaration(t, name+": (): "+string(test.typ)+" = state")
			cfg, metadata, memorySSA, bindings := optIRArm64RegionLoadFixture(t, name, test.typ)
			global := bindings["opaque:state"].Global
			template := &asm.Function{
				Name: name, Arch: asm.ArchArm64, Signature: declaration, Fallback: true,
				Globals: map[string]asm.Global{
					"state":     global,
					"unrelated": {Type: "u64", Bits: 64},
				},
			}
			lowered, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
			if err != nil {
				t.Fatal(err)
			}
			if want := map[string]asm.Global{"state": global}; !reflect.DeepEqual(lowered.Globals, want) {
				t.Fatalf("selected globals = %#v, want %#v", lowered.Globals, want)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, "adrp x17, state") || !strings.Contains(body, test.load) {
				t.Fatalf("selected body lacks its exact global load shape:\n%s", body)
			}
			clobbersScratch := false
			for _, register := range lowered.Clobbers {
				clobbersScratch = clobbersScratch || register.Num == optIRCopyScratch
			}
			if !clobbersScratch {
				t.Fatalf("selected body does not declare address scratch %d: %v", optIRCopyScratch, lowered.Clobbers)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{name: true}); len(findings) != 0 {
				t.Fatalf("selected body fails seam check: %v\n%s", findings, body)
			}
			if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
		})
	}
}

func TestLowerOptIRArm64RegionLoadRequiresAdmittedSite(t *testing.T) {
	const name = "read_region"
	declaration := optIRRV64Declaration(t, name+": (): u32 = state")
	cfg, metadata, memorySSA, bindings := optIRArm64RegionLoadFixture(t, name, "u32")
	template := &asm.Function{
		Name: name, Arch: asm.ArchArm64, Signature: declaration,
		Globals: map[string]asm.Global{"state": {Type: "u32", Bits: 32}},
	}
	memory, err := validateOptIRRegionMemory(cfg, template, metadata, memorySSA, bindings)
	if err != nil {
		t.Fatal(err)
	}
	delete(memory.loads, optir.OperationSite{Block: 0, Index: 0})
	if _, err := lowerOptIRArm64Selection(cfg, template, optIRArm64Registers, optIRArm64SpillRegisters, memory); err == nil || !strings.Contains(err.Error(), "has no admitted global binding") {
		t.Fatalf("AArch64 selector admitted an unbound region-load site: %v", err)
	}
}

func optIRArm64RegionLoadFixture(t *testing.T, name string, typ optir.Type) (optir.CFG, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) {
	t.Helper()
	cfg := optir.CFG{
		Name: name, Entry: 0, Results: []optir.Type{typ},
		Blocks: []optir.Block{{
			ID: 0,
			Operations: []optir.Operation{{
				Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 1, Type: typ}}, Effects: []optir.Effect{optir.EffectReadMemory},
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
		}},
	}
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{"opaque:state"},
		Operations: []optir.MemoryOperationMetadata{{
			Site:     optir.OperationSite{Block: 0, Index: 0},
			Accesses: []optir.MemoryAccessSpec{{Region: "opaque:state", Kind: optir.MemoryRead}},
		}},
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	bits, ok := optIRScalarGlobalBits(typ)
	if !ok {
		t.Fatalf("test type %s is not scalar", typ)
	}
	bindings := map[optir.RegionID]OptIRRegionGlobal{
		"opaque:state": {Symbol: "state", Global: asm.Global{Type: string(typ), Bits: bits}},
	}
	return cfg, metadata, memorySSA, bindings
}
