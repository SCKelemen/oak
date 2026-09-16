package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestRegionLoadForwardingEliminatesDominatedLoadOfSameVersion(t *testing.T) {
	cfg := CFG{
		Name: "repeat_load", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Operations: []Operation{regionLoadOperation(1, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}}},
			{ID: 1, Operations: []Operation{regionLoadOperation(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		regionLoadMetadata(0, 0, "state", false),
		regionLoadMetadata(1, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	want := []RegionLoadReplacement{{
		Access: 2, Site: OperationSite{Block: 1, Index: 0}, Region: "state", Memory: 1,
		Result: 2, Replacement: 1, Kind: RegionLoadFromLoad,
	}}
	if !reflect.DeepEqual(report.Replacements, want) || report.DroppedFacts != 0 {
		t.Fatalf("forwarding report = %+v, want %+v", report, want)
	}
	if len(result.Blocks[0].Operations) != 1 || len(result.Blocks[1].Operations) != 0 || !reflect.DeepEqual(result.Blocks[1].Terminator.Values, []ValueID{1}) {
		t.Fatalf("forwarded CFG = %+v", result)
	}
	if len(resultMetadata.Operations) != 1 || resultMetadata.Operations[0].Site != (OperationSite{Block: 0, Index: 0}) {
		t.Fatalf("forwarded metadata = %+v", resultMetadata)
	}
}

func TestRegionLoadForwardingUsesDominatingWholeRegionStoreAndDropsDependentFacts(t *testing.T) {
	cfg := CFG{
		Name: "store_load", Entry: 0, Results: []Type{"u32"},
		Facts: []Fact{{ID: "result-fact", Name: "same", Values: []ValueID{2}}},
		Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}},
			Operations: []Operation{
				{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
				{Code: OpLoadRegion, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectReadMemory}, Facts: []Fact{{ID: "load-fact", Name: "checked.type", Values: []ValueID{2}}}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
		}},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(0, 1, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if len(report.Replacements) != 1 || report.Replacements[0].Kind != RegionLoadFromStore || report.Replacements[0].Replacement != 1 || report.DroppedFacts != 2 {
		t.Fatalf("store forwarding report = %+v", report)
	}
	if got := result.Blocks[0]; len(got.Operations) != 1 || got.Operations[0].Code != OpStoreRegion || !reflect.DeepEqual(got.Terminator.Values, []ValueID{1}) || len(result.Facts) != 0 {
		t.Fatalf("store-forwarded CFG = %+v", result)
	}
	if len(resultMetadata.Operations) != 1 || resultMetadata.Operations[0].Accesses[0].Kind != MemoryWrite {
		t.Fatalf("store-forwarded metadata = %+v", resultMetadata)
	}
	if len(cfg.Facts) != 1 || len(cfg.Blocks[0].Operations) != 2 {
		t.Fatal("forwarding mutated its input CFG")
	}
}

func TestRegionLoadForwardingCrossesAndPreservesNoModRefCall(t *testing.T) {
	cfg := CFG{
		Name: "store_call_load", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}},
			Operations: []Operation{
				{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
				{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Operands: []ValueID{1}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}}},
				regionLoadOperation(3, "u32"),
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
		}},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		{Site: OperationSite{Block: 0, Index: 1}, CallEffect: MemoryCallNoModRef},
		regionLoadMetadata(0, 2, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 1 || len(result.Blocks[0].Operations) != 2 || !reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{1}) {
		t.Fatalf("NoModRef forwarding result=%+v report=%+v", result, report)
	}
	if got := resultMetadata.Operations; len(got) != 2 || got[1].Site != (OperationSite{Block: 0, Index: 1}) || got[1].CallEffect != MemoryCallNoModRef {
		t.Fatalf("NoModRef forwarding metadata = %+v", got)
	}
}

func TestRegionLoadForwardingCrossesAndPreservesRefCall(t *testing.T) {
	cfg := CFG{
		Name: "store_ref_load", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}},
			Operations: []Operation{
				{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
				{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "read-state"}}},
				regionLoadOperation(3, "u32"),
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
		}},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		{Site: OperationSite{Block: 0, Index: 1}, CallEffect: MemoryCallRef, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryRead}}},
		regionLoadMetadata(0, 2, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 1 || len(result.Blocks[0].Operations) != 2 || !reflect.DeepEqual(result.Blocks[0].Terminator.Values, []ValueID{1}) {
		t.Fatalf("Ref forwarding result=%+v report=%+v", result, report)
	}
	if got := resultMetadata.Operations; len(got) != 2 || got[1].Site != (OperationSite{Block: 0, Index: 1}) ||
		got[1].CallEffect != MemoryCallRef || !reflect.DeepEqual(got[1].Accesses, []MemoryAccessSpec{{Region: "state", Kind: MemoryRead}}) {
		t.Fatalf("Ref forwarding metadata = %+v", got)
	}
}

func TestRegionLoadForwardingStopsAtWriteBearingCall(t *testing.T) {
	for _, test := range []struct {
		name   string
		effect MemoryCallEffect
		kind   MemoryAccessKind
	}{
		{name: "mod", effect: MemoryCallMod, kind: MemoryWrite},
		{name: "mod-ref", effect: MemoryCallModRef, kind: MemoryReadWrite},
	} {
		t.Run(test.name, func(t *testing.T) {
			cfg := CFG{
				Name: "store_call_load", Entry: 0, Results: []Type{"u32"},
				Blocks: []Block{{
					ID: 0, Parameters: []Value{{ID: 1, Type: "u32"}},
					Operations: []Operation{
						{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
						{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "effect"}}},
						regionLoadOperation(3, "u32"),
					},
					Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
				}},
			}
			metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
				{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
				{Site: OperationSite{Block: 0, Index: 1}, CallEffect: test.effect, Accesses: []MemoryAccessSpec{{Region: "state", Kind: test.kind}}},
				regionLoadMetadata(0, 2, "state", false),
			}}
			memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
			result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
			if err != nil {
				t.Fatal(err)
			}
			if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
				t.Fatal(err)
			}
			if report.Changes() != 0 || !sameDeadStoreCFG(result, cfg) || !sameDeadStoreMetadata(t, cfg, metadata, result, resultMetadata) {
				t.Fatalf("forwarded through %s: result=%+v metadata=%+v report=%+v", test.effect, result, resultMetadata, report)
			}
		})
	}
}

func TestRegionLoadForwardingKeepsJoinVersionAndVolatileLoads(t *testing.T) {
	t.Run("join phi", func(t *testing.T) {
		cfg := CFG{
			Name: "join_load", Entry: 0, Results: []Type{"u32"},
			Blocks: []Block{
				{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
				{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
				{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
				{ID: 3, Operations: []Operation{regionLoadOperation(3, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
			},
		}
		metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
			regionLoadMetadata(3, 0, "state", false),
		}}
		memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
		result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
		if err != nil {
			t.Fatal(err)
		}
		before, _ := FingerprintCFG(cfg)
		after, _ := FingerprintCFG(result)
		if report.Changes() != 0 || before != after || len(resultMetadata.Operations) != len(metadata.Operations) {
			t.Fatalf("join load changed: report=%+v cfg=%+v metadata=%+v", report, result, resultMetadata)
		}
	})

	t.Run("volatile", func(t *testing.T) {
		cfg := CFG{
			Name: "volatile_load", Entry: 0, Results: []Type{"u32"},
			Blocks: []Block{{ID: 0, Operations: []Operation{regionLoadOperation(1, "u32"), regionLoadOperation(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}}},
		}
		metadata := RegionMemoryMetadata{Regions: []RegionID{"device"}, Operations: []MemoryOperationMetadata{
			regionLoadMetadata(0, 0, "device", true),
			regionLoadMetadata(0, 1, "device", true),
		}}
		memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
		result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
		if err != nil {
			t.Fatal(err)
		}
		before, _ := FingerprintCFG(cfg)
		after, _ := FingerprintCFG(result)
		if report.Changes() != 0 || before != after || len(resultMetadata.Operations) != len(metadata.Operations) {
			t.Fatalf("volatile loads changed: report=%+v", report)
		}
	})
}

func TestRegionLoadForwardingVerifierRejectsStaleAndMutatedEvidence(t *testing.T) {
	cfg := CFG{
		Name: "verify_forward", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{{ID: 0, Operations: []Operation{regionLoadOperation(1, "u32"), regionLoadOperation(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}}},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		regionLoadMetadata(0, 0, "state", false), regionLoadMetadata(0, 1, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	mutated := report
	mutated.Replacements = append([]RegionLoadReplacement(nil), report.Replacements...)
	mutated.Replacements[0].Replacement = 99
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, mutated); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("mutated report verification = %v", err)
	}
	staleResult := cloneCFG(result)
	staleResult.Name = "stale"
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, staleResult, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "different output CFG") {
		t.Fatalf("stale output verification = %v", err)
	}
	staleMetadata := RegionMemoryMetadata{Regions: []RegionID{"other"}, Operations: resultMetadata.Operations}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, staleMetadata, report); err == nil || !strings.Contains(err.Error(), "undeclared region") {
		t.Fatalf("stale output metadata verification = %v", err)
	}
	mutatedSSA := memorySSA
	mutatedSSA.Accesses = append([]MemoryAccess(nil), memorySSA.Accesses...)
	mutatedSSA.Accesses[0].Input++
	if err := VerifyRegionLoadForwarding(cfg, metadata, mutatedSSA, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("mutated MemorySSA verification = %v", err)
	}
}

func regionLoadOperation(result ValueID, typ Type) Operation {
	return Operation{Code: OpLoadRegion, Results: []Value{{ID: result, Type: typ}}, Effects: []Effect{EffectReadMemory}}
}

func regionLoadMetadata(block BlockID, index int, region RegionID, volatile bool) MemoryOperationMetadata {
	return MemoryOperationMetadata{Site: OperationSite{Block: block, Index: index}, Accesses: []MemoryAccessSpec{{Region: region, Kind: MemoryRead, Volatile: volatile}}}
}

func mustRegionLoadMemorySSA(t *testing.T, cfg CFG, metadata RegionMemoryMetadata) RegionMemorySSA {
	t.Helper()
	memorySSA, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	return memorySSA
}
