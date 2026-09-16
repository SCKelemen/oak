package machine

import (
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRRegionStoreVerifiesOnBothNativeTargets(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
set_region: (x: u32): () = {
  state = x
}
`)
	cfg, metadata, memorySSA, bindings := optIRRegionStoreFixture(t, "set_region", "u32")
	wantGlobals := map[string]asm.Global{"state": {Type: "u32", Bits: 32}}
	tests := []struct {
		name    string
		arch    string
		binding asm.Binding
		address string
		store   string
		scratch int
		lower   func(optir.CFG, *asm.Function, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
	}{
		{name: "aarch64", arch: asm.ArchArm64, binding: asm.Binding{Register: w(0), Param: "x"}, address: "adrp x17, state", store: "str w0, [x17,#0]", scratch: 17, lower: LowerOptIRArm64WithRegionMemory},
		{name: "rv64", arch: asm.ArchRV64, binding: asm.Binding{Register: optIRRV64Register(10), Param: "x"}, address: "la t6, state", store: "sw a0, [t6,#0]", scratch: 31, lower: LowerOptIRRV64WithRegionMemory},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			template := &asm.Function{
				Name: "set_region", Arch: test.arch, Signature: declaration, Fallback: true,
				Bindings: []asm.Binding{test.binding},
				// Unrelated template state must not leak into the selected body.
				Globals: map[string]asm.Global{
					"state":     {Type: "u32", Bits: 32},
					"unrelated": {Type: "u64", Bits: 64},
				},
			}
			lowered, err := test.lower(cfg, template, metadata, memorySSA, bindings)
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(lowered.Globals, wantGlobals) {
				t.Fatalf("selected globals = %#v, want %#v", lowered.Globals, wantGlobals)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, test.address) || !strings.Contains(body, test.store) {
				t.Fatalf("selected body lacks its exact global address/store shape:\n%s", body)
			}
			clobbersScratch := false
			for _, register := range lowered.Clobbers {
				clobbersScratch = clobbersScratch || register.Num == test.scratch
			}
			if !clobbersScratch {
				t.Fatalf("selected body does not declare address scratch %d: %v", test.scratch, lowered.Clobbers)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{"set_region": true}); len(findings) != 0 {
				t.Fatalf("selected body fails seam check: %v\n%s", findings, body)
			}
			if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
		})
	}
}

func TestLowerOptIRBoolRegionStoreUsesCanonicalPackageCell(t *testing.T) {
	declaration := optIRRV64Declaration(t, `
set_flag: (x: Bool): () = {
  state = x
}
`)
	cfg, metadata, memorySSA, bindings := optIRRegionStoreFixture(t, "set_flag", optir.TypeBool)
	tests := []struct {
		name    string
		arch    string
		binding asm.Binding
		store   string
		lower   func(optir.CFG, *asm.Function, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
	}{
		{name: "aarch64", arch: asm.ArchArm64, binding: asm.Binding{Register: w(0), Param: "x"}, store: "str w0, [x17,#0]", lower: LowerOptIRArm64WithRegionMemory},
		{name: "rv64", arch: asm.ArchRV64, binding: asm.Binding{Register: optIRRV64Register(10), Param: "x"}, store: "sw a0, [t6,#0]", lower: LowerOptIRRV64WithRegionMemory},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			template := &asm.Function{
				Name: "set_flag", Arch: test.arch, Signature: declaration, Fallback: true,
				Bindings: []asm.Binding{test.binding},
				Globals:  map[string]asm.Global{"state": {Type: "Bool", Bits: 32}},
			}
			lowered, err := test.lower(cfg, template, metadata, memorySSA, bindings)
			if err != nil {
				t.Fatal(err)
			}
			body := text(lowered.Items)
			if !strings.Contains(body, test.store) || strings.Contains(body, "strb ") || strings.Contains(body, "sb ") {
				t.Fatalf("Bool was not stored through its canonical 32-bit package cell:\n%s", body)
			}
			if global := lowered.Globals["state"]; global.Type != "Bool" || global.Bits != 32 {
				t.Fatalf("Bool global descriptor = %#v", global)
			}
			if findings := asm.Check(lowered, declaration, map[string]bool{"set_flag": true}); len(findings) != 0 {
				t.Fatalf("selected Bool body fails seam check: %v\n%s", findings, body)
			}
			if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
				t.Fatalf("selected Bool body verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
			}
		})
	}
}

func TestLowerOptIRRegionStoreEvidenceAndBindingsFailClosed(t *testing.T) {
	lower := func(cfg optir.CFG, metadata optir.RegionMemoryMetadata, memorySSA optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) error {
		declaration := optIRRV64Declaration(t, `set_region: (x: u32): () = { state = x }`)
		template := &asm.Function{
			Name: "set_region", Arch: asm.ArchArm64, Signature: declaration,
			Bindings: []asm.Binding{{Register: w(0), Param: "x"}},
			Globals:  map[string]asm.Global{"state": {Type: "u32", Bits: 32}},
		}
		_, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
		return err
	}
	assertRefused := func(name, want string, mutate func(*optir.CFG, *optir.RegionMemoryMetadata, *optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal)) {
		t.Helper()
		t.Run(name, func(t *testing.T) {
			cfg, metadata, memorySSA, bindings := optIRRegionStoreFixture(t, "set_region", "u32")
			mutate(&cfg, &metadata, &memorySSA, bindings)
			if err := lower(cfg, metadata, memorySSA, bindings); err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("error = %v, want refusal containing %q", err, want)
			}
		})
	}

	assertRefused("mutated SSA", "was mutated", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		memorySSA.Accesses[0].WholeRegion = false
	})
	assertRefused("stale SSA", "different metadata", func(_ *optir.CFG, metadata *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		metadata.Operations[0].Accesses[0].Volatile = true
	})
	assertRefused("missing binding", "bindings for", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		delete(bindings, "global:state")
	})
	assertRefused("extra binding", "bindings for", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		bindings["global:other"] = OptIRRegionGlobal{Symbol: "other", Global: asm.Global{Type: "u32", Bits: 32}}
	})
	assertRefused("wrong type", "storage is i32/32", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		bindings["global:state"] = OptIRRegionGlobal{Symbol: "state", Global: asm.Global{Type: "i32", Bits: 32}}
	})
	assertRefused("wrong width", "storage is u32/64", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		bindings["global:state"] = OptIRRegionGlobal{Symbol: "state", Global: asm.Global{Type: "u32", Bits: 64}}
	})
	assertRefused("aggregate", "outside the scalar", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		bindings["global:state"] = OptIRRegionGlobal{Symbol: "state", Global: asm.Global{Type: "u32", Aggregate: true, Size: 4}}
	})
	assertRefused("empty symbol", "empty global symbol", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) {
		bindings["global:state"] = OptIRRegionGlobal{Global: asm.Global{Type: "u32", Bits: 32}}
	})
	assertRefused("malformed store", "not a canonical region store", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		cfg.Blocks[0].Operations[0].Attributes = []optir.Attribute{{Name: "mode", Value: "device"}}
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})
	assertRefused("partial store", "not one whole nonvolatile write", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		metadata.Operations[0].Accesses[0].WholeRegion = false
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})
	assertRefused("volatile store", "not one whole nonvolatile write", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		metadata.Operations[0].Accesses[0].Volatile = true
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})
	assertRefused("read access", "want exactly one memory-write effect", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		cfg.Blocks[0].Operations[0].Effects = []optir.Effect{optir.EffectReadMemory}
		metadata.Operations[0].Accesses[0] = optir.MemoryAccessSpec{Region: "global:state", Kind: optir.MemoryRead}
	})
	assertRefused("unknown clobber", "unsupported access kind", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		cfg.Blocks[0].Operations[0] = optir.Operation{
			Code: optir.OpCall, Results: []optir.Value{{ID: 3, Type: "()"}}, Effects: []optir.Effect{optir.EffectCall},
			Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: "opaque"}},
		}
		metadata.Operations[0].Accesses[0] = optir.MemoryAccessSpec{Kind: optir.MemoryUnknownClobber}
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})
	assertRefused("control flow", "one straight-line", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA, _ map[optir.RegionID]OptIRRegionGlobal) {
		unit := cfg.Blocks[0].Operations[1]
		cfg.Blocks[0].Operations = cfg.Blocks[0].Operations[:1]
		cfg.Blocks[0].Terminator = optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 1}}
		cfg.Blocks = append(cfg.Blocks, optir.Block{ID: 1, Operations: []optir.Operation{unit}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}}})
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})

	cfg, metadata, _, bindings := optIRRegionStoreFixture(t, "set_region", "u32")
	declaration := optIRRV64Declaration(t, `set_region: (x: u32): () = { state = x }`)
	template := &asm.Function{Name: "set_region", Arch: asm.ArchArm64, Signature: declaration, Bindings: []asm.Binding{{Register: w(0), Param: "x"}}}
	if _, err := LowerOptIRArm64(cfg, template); err == nil || !strings.Contains(err.Error(), "effectful operation") {
		t.Fatalf("pure selector admitted memory operation: %v", err)
	}
	if _, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, optir.RegionMemorySSA{}, bindings); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("selector admitted absent MemorySSA evidence: %v", err)
	}
}

func TestLowerOptIRRegionLoadEvidenceAndShapeFailClosed(t *testing.T) {
	lower := func(cfg optir.CFG, metadata optir.RegionMemoryMetadata, memorySSA optir.RegionMemorySSA, bindings map[optir.RegionID]OptIRRegionGlobal) error {
		declaration := optIRRV64Declaration(t, `read_region: (): u32 = state`)
		template := &asm.Function{
			Name: "read_region", Arch: asm.ArchArm64, Signature: declaration,
			Globals: map[string]asm.Global{"state": {Type: "u32", Bits: 32}},
		}
		_, err := LowerOptIRArm64WithRegionMemory(cfg, template, metadata, memorySSA, bindings)
		return err
	}
	assertRefused := func(name, want string, mutate func(*optir.CFG, *optir.RegionMemoryMetadata, *optir.RegionMemorySSA)) {
		t.Helper()
		t.Run(name, func(t *testing.T) {
			cfg, metadata, memorySSA, bindings := optIRArm64RegionLoadFixture(t, "read_region", "u32")
			mutate(&cfg, &metadata, &memorySSA)
			if err := lower(cfg, metadata, memorySSA, bindings); err == nil || !strings.Contains(err.Error(), want) {
				t.Fatalf("error = %v, want refusal containing %q", err, want)
			}
		})
	}

	assertRefused("mutated SSA", "was mutated", func(_ *optir.CFG, _ *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA) {
		memorySSA.Accesses[0].WholeRegion = true
	})
	assertRefused("stale metadata", "different metadata", func(_ *optir.CFG, metadata *optir.RegionMemoryMetadata, _ *optir.RegionMemorySSA) {
		metadata.Operations[0].Accesses[0].Volatile = true
	})
	assertRefused("load attributes", "not a canonical nonvolatile region load", func(cfg *optir.CFG, metadata *optir.RegionMemoryMetadata, memorySSA *optir.RegionMemorySSA) {
		cfg.Blocks[0].Operations[0].Attributes = []optir.Attribute{{Name: "ordering", Value: "relaxed"}}
		*memorySSA = optIRAnalyzeRegionMemory(t, *cfg, *metadata)
	})
}

func TestLowerOptIRRegionStoreRequiresTemplateGlobalAuthority(t *testing.T) {
	cfg, metadata, memorySSA, bindings := optIRRegionStoreFixture(t, "set_region", "u32")
	declaration := optIRRV64Declaration(t, `set_region: (x: u32): () = { state = x }`)
	template := func(globals map[string]asm.Global) *asm.Function {
		return &asm.Function{
			Name: "set_region", Arch: asm.ArchArm64, Signature: declaration,
			Bindings: []asm.Binding{{Register: w(0), Param: "x"}}, Globals: globals,
		}
	}
	if _, err := LowerOptIRArm64WithRegionMemory(cfg, template(nil), metadata, memorySSA, bindings); err == nil || !strings.Contains(err.Error(), "not authorized") {
		t.Fatalf("selector admitted a global absent from template authority: %v", err)
	}
	if _, err := LowerOptIRArm64WithRegionMemory(cfg, template(map[string]asm.Global{"state": {Type: "u32", Bits: 64}}), metadata, memorySSA, bindings); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("selector admitted a descriptor that disagrees with template authority: %v", err)
	}
}

func TestLowerOptIRRegionStoresRefuseRegisterSpills(t *testing.T) {
	store := optir.Operation{Code: optir.OpStoreRegion, Operands: []optir.ValueID{1}, Effects: []optir.Effect{optir.EffectWriteMemory}}
	cfg := optir.CFG{
		Name: "pressure_store", Entry: 0, Results: []optir.Type{"u32"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: "u32", Name: "x"}},
			Operations: []optir.Operation{
				{Code: optir.OpConstInt, Results: []optir.Value{{ID: 2, Type: "u32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "1"}}},
				store,
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{"global:state"},
		Operations: []optir.MemoryOperationMetadata{{
			Site:     optir.OperationSite{Block: 0, Index: 1},
			Accesses: []optir.MemoryAccessSpec{{Region: "global:state", Kind: optir.MemoryWrite, WholeRegion: true}},
		}},
	}
	memorySSA := optIRAnalyzeRegionMemory(t, cfg, metadata)
	authorized := map[string]asm.Global{"state": {Type: "u32", Bits: 32}}
	memory, err := validateOptIRRegionMemory(cfg, &asm.Function{Globals: authorized}, metadata, memorySSA, map[optir.RegionID]OptIRRegionGlobal{
		"global:state": {Symbol: "state", Global: asm.Global{Type: "u32", Bits: 32}},
	})
	if err != nil {
		t.Fatal(err)
	}
	declaration := optIRRV64Declaration(t, `pressure_store: (x: u32): u32 = { state = x; u32(1) }`)
	armTemplate := &asm.Function{Name: "pressure_store", Arch: asm.ArchArm64, Signature: declaration, Bindings: []asm.Binding{{Register: w(0), Param: "x"}}, Globals: authorized}
	if _, err := lowerOptIRArm64Selection(cfg, armTemplate, []int{0}, []int{0}, memory); err == nil || !strings.Contains(err.Error(), "register spills") {
		t.Fatalf("AArch64 memory selector admitted spills: %v", err)
	}
	rvTemplate := &asm.Function{Name: "pressure_store", Arch: asm.ArchRV64, Signature: declaration, Bindings: []asm.Binding{{Register: optIRRV64Register(10), Param: "x"}}, Globals: authorized}
	if _, err := lowerOptIRRV64Selection(cfg, rvTemplate, []int{10}, []int{5}, memory); err == nil || !strings.Contains(err.Error(), "register spills") {
		t.Fatalf("RV64 memory selector admitted spills: %v", err)
	}
}

func optIRRegionStoreFixture(t *testing.T, name string, typ optir.Type) (optir.CFG, optir.RegionMemoryMetadata, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) {
	t.Helper()
	cfg := optir.CFG{
		Name: name, Entry: 0, Results: []optir.Type{"()"},
		Blocks: []optir.Block{{
			ID: 0, Parameters: []optir.Value{{ID: 1, Type: typ, Name: "x"}},
			Operations: []optir.Operation{
				{Code: optir.OpStoreRegion, Operands: []optir.ValueID{1}, Effects: []optir.Effect{optir.EffectWriteMemory}},
				{Code: optir.OpConstUnit, Results: []optir.Value{{ID: 2, Type: "()"}}},
			},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{2}},
		}},
	}
	metadata := optir.RegionMemoryMetadata{
		Regions: []optir.RegionID{"global:state"},
		Operations: []optir.MemoryOperationMetadata{{
			Site:     optir.OperationSite{Block: 0, Index: 0},
			Accesses: []optir.MemoryAccessSpec{{Region: "global:state", Kind: optir.MemoryWrite, WholeRegion: true}},
		}},
	}
	memorySSA := optIRAnalyzeRegionMemory(t, cfg, metadata)
	bits, ok := optIRScalarGlobalBits(typ)
	if !ok {
		t.Fatalf("test type %s is not scalar", typ)
	}
	bindings := map[optir.RegionID]OptIRRegionGlobal{
		"global:state": {Symbol: "state", Global: asm.Global{Type: string(typ), Bits: bits}},
	}
	return cfg, metadata, memorySSA, bindings
}

func optIRAnalyzeRegionMemory(t *testing.T, cfg optir.CFG, metadata optir.RegionMemoryMetadata) optir.RegionMemorySSA {
	t.Helper()
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	return memorySSA
}
