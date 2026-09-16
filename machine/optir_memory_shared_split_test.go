package machine

import (
	"fmt"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

func TestLowerOptIRSharedMemorySplitVerifiesOnBothNativeTargets(t *testing.T) {
	for _, known := range []string{"", "left", "right"} {
		name := known + " available"
		if known == "" {
			name = "both moved"
		}
		t.Run(name, func(t *testing.T) {
			initial := ""
			if known != "" {
				initial = known + " = y"
			}
			declaration := optIRRV64Declaration(t, fmt.Sprintf(`
shared_loads: (set: Bool, x: u32, y: u32): u32 = {
  %s
  set ? {
    left = x
    right = y
  } | {
    unused: Bool = set
  }
  left + right
}
`, initial))
			var records []optir.CheckedMemoryAccessRecord
			operation := func(region string, kind optir.MemoryAccessKind, value optir.ValueID) optir.Operation {
				t.Helper()
				source := optir.Source{Context: "shared-split.oak", Line: len(records) + 1, Column: 1}
				record, err := optir.NewCheckedMemoryAccessRecord(source, optir.RegionID(region), kind, "u32", kind == optir.MemoryWrite, false)
				if err != nil {
					t.Fatal(err)
				}
				records = append(records, record)
				op := optir.Operation{Source: source, MemoryAccessID: record.ID}
				if kind == optir.MemoryWrite {
					op.Code, op.Operands, op.Effects = optir.OpStoreRegion, []optir.ValueID{value}, []optir.Effect{optir.EffectWriteMemory}
				} else {
					op.Code, op.Results, op.Effects = optir.OpLoadRegion, []optir.Value{{ID: value, Type: "u32", Source: source}}, []optir.Effect{optir.EffectReadMemory}
				}
				return op
			}
			cfg := optir.CFG{
				Name: "shared_loads", Entry: 0, Results: []optir.Type{"u32"},
				Blocks: []optir.Block{
					{ID: 0, Parameters: []optir.Value{{ID: 1, Type: optir.TypeBool, Name: "set"}, {ID: 2, Type: "u32", Name: "x"}, {ID: 3, Type: "u32", Name: "y"}}, Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 1, True: optir.Edge{Target: 1}, False: optir.Edge{Target: 3}}},
					{ID: 1, Operations: []optir.Operation{operation("left", optir.MemoryWrite, 2), operation("right", optir.MemoryWrite, 3)}, Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 3}}},
					{ID: 3, Operations: []optir.Operation{
						operation("left", optir.MemoryRead, 4), operation("right", optir.MemoryRead, 5),
						{Code: optir.OpIntAdd, Results: []optir.Value{{ID: 6, Type: "u32"}}, Operands: []optir.ValueID{4, 5}},
					}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{6}}},
				},
			}
			if known != "" {
				cfg.Blocks[0].Operations = []optir.Operation{operation(known, optir.MemoryWrite, 3)}
			}
			authority, err := optir.NewCheckedMemoryAuthority(records)
			if err != nil {
				t.Fatal(err)
			}
			projection, err := optir.ProjectCheckedMemory(cfg, authority)
			if err != nil {
				t.Fatal(err)
			}
			inputSSA := optIRAnalyzeRegionMemory(t, cfg, projection.Metadata)
			optimized, metadata, report, err := optir.ForwardRegionLoads(cfg, projection.Metadata, inputSSA)
			if err != nil {
				t.Fatal(err)
			}
			if err := optir.VerifyRegionLoadForwarding(cfg, projection.Metadata, inputSSA, optimized, metadata, report); err != nil {
				t.Fatal(err)
			}
			wantInsertions := 2
			if known != "" {
				wantInsertions = 1
			}
			if len(optimized.Blocks) != 4 || len(report.Replacements) != 2 || len(report.Insertions) != wantInsertions || len(optimized.Blocks[2].Operations) != 1 {
				t.Fatalf("both join loads must be promoted through one split: %+v", report)
			}
			for _, insertion := range report.Insertions {
				if !insertion.Split || insertion.Site.Block != 4 {
					t.Fatalf("load did not use the shared edge: %+v", insertion)
				}
			}
			finalProjection, err := optir.ProjectCheckedMemory(optimized, authority)
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(finalProjection.Metadata, metadata) {
				t.Fatalf("checked authority disagrees with transformed metadata: %+v, want %+v", finalProjection.Metadata, metadata)
			}
			if wantInsertions == 2 {
				forged := optimized
				forged.Blocks = append([]optir.Block(nil), optimized.Blocks...)
				split := &forged.Blocks[3]
				split.Operations = append([]optir.Operation(nil), split.Operations...)
				split.Operations[1].MemoryAccessID = split.Operations[0].MemoryAccessID
				if _, err := optir.ProjectCheckedMemory(forged, authority); err == nil {
					t.Fatal("shared edge accepted duplicated checked load authority")
				}
			}
			finalSSA := optIRAnalyzeRegionMemory(t, optimized, metadata)
			bindings := map[optir.RegionID]OptIRRegionGlobal{
				"left":  {Symbol: "left", Global: asm.Global{Type: "u32", Bits: 32}},
				"right": {Symbol: "right", Global: asm.Global{Type: "u32", Bits: 32}},
			}
			for _, target := range []struct {
				arch  string
				regs  []asm.Binding
				lower func(optir.CFG, *asm.Function, optir.CheckedMemoryAuthority, optir.CheckedMemoryProjection, optir.RegionMemorySSA, map[optir.RegionID]OptIRRegionGlobal) (*asm.Function, error)
			}{
				{arch: asm.ArchArm64, regs: []asm.Binding{{Register: w(0), Param: "set"}, {Register: w(1), Param: "x"}, {Register: w(2), Param: "y"}}, lower: LowerOptIRArm64WithCheckedRegionMemory},
				{arch: asm.ArchRV64, regs: []asm.Binding{{Register: optIRRV64Register(10), Param: "set"}, {Register: optIRRV64Register(11), Param: "x"}, {Register: optIRRV64Register(12), Param: "y"}}, lower: LowerOptIRRV64WithCheckedRegionMemory},
			} {
				t.Run(target.arch, func(t *testing.T) {
					template := &asm.Function{
						Name: cfg.Name, Arch: target.arch, Signature: declaration, Fallback: true, Bindings: target.regs,
						Globals: map[string]asm.Global{"left": {Type: "u32", Bits: 32}, "right": {Type: "u32", Bits: 32}},
					}
					lowered, err := target.lower(optimized, template, authority, finalProjection, finalSSA, bindings)
					if err != nil {
						t.Fatal(err)
					}
					body := text(lowered.Items)
					if findings := asm.Check(lowered, declaration, map[string]bool{cfg.Name: true}); len(findings) != 0 {
						t.Fatalf("shared split fails seam admission: %v\n%s", findings, body)
					}
					if verdict := asm.Verify(lowered, declaration, declaration.Body); verdict.Kind != asm.VerdictProven {
						t.Fatalf("shared split verdict = %s (%s)\n%s", verdict.Kind, verdict.Message, body)
					}
				})
			}
		})
	}
}
