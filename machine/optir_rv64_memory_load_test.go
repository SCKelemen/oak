package machine

import (
	"fmt"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRRV64RegionLoadsVerifyForEveryScalarWidth(t *testing.T) {
	tests := []struct {
		typ      optir.Type
		mnemonic string
	}{
		{typ: optir.TypeBool, mnemonic: "lw"},
		{typ: "u8", mnemonic: "lbu"},
		{typ: "i8", mnemonic: "lb"},
		{typ: "u16", mnemonic: "lhu"},
		{typ: "i16", mnemonic: "lh"},
		{typ: "u32", mnemonic: "lw"},
		{typ: "i32", mnemonic: "lw"},
		{typ: "u64", mnemonic: "ld"},
		{typ: "i64", mnemonic: "ld"},
	}
	for _, test := range tests {
		t.Run(string(test.typ), func(t *testing.T) {
			declaration := optIRRV64Declaration(t, fmt.Sprintf(`load_region: (): %s = { state }`, test.typ))
			cfg, metadata, memorySSA, bindings := optIRRV64RegionLoadFixture(t, test.typ)
			global := bindings["checked-region"].Global
			template := &asm.Function{
				Name: "load_region", Arch: asm.ArchRV64, Signature: declaration, Fallback: true,
				Globals: map[string]asm.Global{
					"state":     global,
					"unrelated": {Type: "u64", Bits: 64},
				},
			}

			lowered, err := LowerOptIRRV64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
			if err != nil {
				t.Fatal(err)
			}
			wantGlobals := map[string]asm.Global{"state": global}
			if !reflect.DeepEqual(lowered.Globals, wantGlobals) {
				t.Fatalf("selected globals = %#v, want %#v", lowered.Globals, wantGlobals)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, "la t6, state") || !strings.Contains(body, test.mnemonic+" t0, [t6,#0]") {
				t.Fatalf("selected body lacks exact %s region load:\n%s", test.mnemonic, body)
			}
			for _, wrong := range []string{"lbu", "lb", "lhu", "lh", "lw", "ld"} {
				if wrong != test.mnemonic && strings.Contains(body, wrong+" t0, [t6,#0]") {
					t.Fatalf("selected body also contains wrong-width load %s:\n%s", wrong, body)
				}
			}
			if !optIRRV64HasClobber(lowered, optIRRV64CopyScratch) {
				t.Fatalf("selected body does not declare address scratch t6: %v", lowered.Clobbers)
			}
			if !optIRRV64HasClobber(lowered, 5) {
				t.Fatalf("selected body does not declare load destination t0: %v", lowered.Clobbers)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{"load_region": true}); len(findings) != 0 {
				t.Fatalf("selected body fails seam check: %v\n%s", findings, body)
			}
			if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
		})
	}
}

func TestLowerOptIRRV64PureSelectorRefusesRegionLoad(t *testing.T) {
	declaration := optIRRV64Declaration(t, `load_region: (): u32 = { state }`)
	cfg, _, _, _ := optIRRV64RegionLoadFixture(t, "u32")
	template := &asm.Function{Name: "load_region", Arch: asm.ArchRV64, Signature: declaration}
	if _, err := LowerOptIRRV64(cfg, template); err == nil || !strings.Contains(err.Error(), "effectful operation") {
		t.Fatalf("pure selector admitted a region load: %v", err)
	}
}

func optIRRV64RegionLoadFixture(t *testing.T, typ optir.Type) (optir.CFG, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) {
	t.Helper()
	cfg := optir.CFG{
		Name: "load_region", Entry: 0, Results: []optir.Type{typ},
		Blocks: []optir.Block{{
			ID: 0,
			Operations: []optir.Operation{{
				Code: optir.OpLoadRegion, Results: []optir.Value{{ID: 1, Type: typ}}, Effects: []optir.Effect{optir.EffectReadMemory},
			}},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
		}},
	}
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{"checked-region"},
		Operations: []optir.MemoryOperationMetadata{{
			Site:     optir.OperationSite{Block: 0, Index: 0},
			Accesses: []optir.MemoryAccessSpec{{Region: "checked-region", Kind: optir.MemoryRead}},
		}},
	}
	memorySSA := optIRAnalyzeRegionMemory(t, cfg, metadata)
	bits, ok := optIRScalarGlobalBits(typ)
	if !ok {
		t.Fatalf("test type %s is not scalar", typ)
	}
	bindings := map[optir.RegionID]OptIRRegionGlobal{
		"checked-region": {Symbol: "state", Global: asm.Global{Type: string(typ), Bits: bits}},
	}
	return cfg, metadata, memorySSA, bindings
}

func optIRRV64HasClobber(function *asm.Function, register int) bool {
	for _, clobber := range function.Clobbers {
		if clobber.Num == register {
			return true
		}
	}
	return false
}
