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

func TestRegionLoadForwardingReplacesJoinLoadWithEdgeSuppliedParameter(t *testing.T) {
	cfg := CFG{
		Name: "join_stores", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{2}}}},
			{ID: 2, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3, Arguments: []ValueID{3}}}},
			{
				ID: 3, Parameters: []Value{{ID: 4, Type: "u32"}},
				Operations: []Operation{
					regionLoadOperation(5, "u32"),
					{Code: OpIntAdd, Results: []Value{{ID: 6, Type: "u32"}}, Operands: []ValueID{4, 5}},
				},
				Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{6}},
			},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		{Site: OperationSite{Block: 2, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(3, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	wantReplacement := RegionLoadReplacement{
		Access: 3, Site: OperationSite{Block: 3, Index: 0}, Region: "state", Memory: 2,
		Result: 5, Replacement: 7, Kind: RegionLoadFromPhi,
	}
	if !reflect.DeepEqual(report.Replacements, []RegionLoadReplacement{wantReplacement}) {
		t.Fatalf("memory-phi forwarding report = %+v, want %+v", report.Replacements, wantReplacement)
	}
	join := result.Blocks[3]
	if len(join.Parameters) != 2 || join.Parameters[1].ID != 7 || join.Parameters[1].Type != "u32" || len(join.Operations) != 1 ||
		!reflect.DeepEqual(join.Operations[0].Operands, []ValueID{4, 7}) {
		t.Fatalf("memory-phi join = %+v", join)
	}
	if !reflect.DeepEqual(result.Blocks[1].Terminator.True.Arguments, []ValueID{2, 2}) ||
		!reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{3, 3}) {
		t.Fatalf("memory-phi edge arguments = then %v else %v", result.Blocks[1].Terminator.True.Arguments, result.Blocks[2].Terminator.True.Arguments)
	}
	if len(resultMetadata.Operations) != 2 || resultMetadata.Operations[0].Site != (OperationSite{Block: 1, Index: 0}) || resultMetadata.Operations[1].Site != (OperationSite{Block: 2, Index: 0}) {
		t.Fatalf("memory-phi metadata = %+v", resultMetadata)
	}
	if len(cfg.Blocks[3].Parameters) != 1 || len(cfg.Blocks[1].Terminator.True.Arguments) != 1 {
		t.Fatal("memory-phi forwarding mutated its input CFG")
	}
}

func TestRegionLoadForwardingReplacesJoinLoadWithAvailablePredecessorLoad(t *testing.T) {
	cfg := CFG{
		Name: "join_store_load", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 4}}},
			{ID: 3, Operations: []Operation{regionLoadOperation(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
			{ID: 4, Operations: []Operation{regionLoadOperation(3, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(3, 0, "state", false),
		regionLoadMetadata(4, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	wantReplacement := RegionLoadReplacement{
		Access: 2, Site: OperationSite{Block: 3, Index: 0}, Region: "state", Memory: 2,
		Result: 4, Replacement: 5, Kind: RegionLoadFromPhi,
	}
	if !reflect.DeepEqual(report.Replacements, []RegionLoadReplacement{wantReplacement}) {
		t.Fatalf("available-load memory-phi report = %+v, want %+v", report.Replacements, wantReplacement)
	}
	join := result.Blocks[3]
	if len(join.Parameters) != 1 || join.Parameters[0].ID != 5 || join.Parameters[0].Type != "u32" || len(join.Operations) != 0 ||
		!reflect.DeepEqual(join.Terminator.Values, []ValueID{5}) {
		t.Fatalf("available-load memory-phi join = %+v", join)
	}
	if !reflect.DeepEqual(result.Blocks[1].Terminator.True.Arguments, []ValueID{2}) ||
		!reflect.DeepEqual(result.Blocks[4].Terminator.True.Arguments, []ValueID{3}) {
		t.Fatalf("available-load memory-phi edge arguments = store %v load %v", result.Blocks[1].Terminator.True.Arguments, result.Blocks[4].Terminator.True.Arguments)
	}
	if len(result.Blocks[4].Operations) != 1 || len(resultMetadata.Operations) != 2 {
		t.Fatalf("predecessor load was not preserved: CFG %+v, metadata %+v", result, resultMetadata)
	}
}

func TestRegionLoadForwardingResolvesRemovedPredecessorLoad(t *testing.T) {
	cfg := CFG{
		Name: "join_removed_load", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{
				ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}},
				Operations: []Operation{regionLoadOperation(3, "u32")},
				Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}},
			},
			{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 4}}},
			{ID: 3, Operations: []Operation{regionLoadOperation(5, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
			{ID: 4, Operations: []Operation{regionLoadOperation(4, "u32")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		regionLoadMetadata(0, 0, "state", false),
		{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(3, 0, "state", false),
		regionLoadMetadata(4, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 2 || report.Replacements[0].Kind != RegionLoadFromPhi || report.Replacements[0].Result != 5 || report.Replacements[0].Replacement != 6 ||
		report.Replacements[1].Kind != RegionLoadFromLoad || report.Replacements[1].Result != 4 || report.Replacements[1].Replacement != 3 {
		t.Fatalf("removed predecessor-load report = %+v", report.Replacements)
	}
	if !reflect.DeepEqual(result.Blocks[4].Terminator.True.Arguments, []ValueID{3}) || len(result.Blocks[4].Operations) != 0 {
		t.Fatalf("removed predecessor-load edge = %+v", result.Blocks[4])
	}
	if len(result.Blocks[3].Parameters) != 1 || result.Blocks[3].Parameters[0].ID != 6 || !reflect.DeepEqual(result.Blocks[3].Terminator.Values, []ValueID{6}) {
		t.Fatalf("removed predecessor-load join = %+v", result.Blocks[3])
	}
	if len(resultMetadata.Operations) != 2 {
		t.Fatalf("removed predecessor-load metadata = %+v", resultMetadata)
	}
}

func TestRegionLoadForwardingMemoryPhiRefusesValueIDOverflow(t *testing.T) {
	cfg := CFG{
		Name: "join_overflow", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}, {ID: ^ValueID(0), Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 2, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 3, Operations: []Operation{regionLoadOperation(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		{Site: OperationSite{Block: 2, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(3, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	if _, _, _, err := ForwardRegionLoads(cfg, metadata, memorySSA); err == nil || !strings.Contains(err.Error(), "value identity overflow") {
		t.Fatalf("memory-phi overflow = %v", err)
	}
}

func TestRegionLoadForwardingMaterializedEdgeRefusesSecondValueIDOverflow(t *testing.T) {
	cfg := CFG{
		Name: "join_edge_overflow", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: ^ValueID(0) - 1, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
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
	if _, _, _, err := ForwardRegionLoads(cfg, metadata, memorySSA); err == nil || !strings.Contains(err.Error(), "value identity overflow") {
		t.Fatalf("materialized edge overflow = %v", err)
	}
}

func TestRegionLoadForwardingPromotesLoopHeaderPhi(t *testing.T) {
	cfg := CFG{
		Name: "loop_stores", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{
				ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}, {ID: 3, Type: "u32"}},
				Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}},
			},
			{
				ID: 1, Operations: []Operation{regionLoadOperation(4, "u32")},
				Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 2}, False: Edge{Target: 3, Arguments: []ValueID{4}}},
			},
			{
				ID: 2, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}}},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}},
			},
			{ID: 3, Parameters: []Value{{ID: 5, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{5}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		{Site: OperationSite{Block: 0, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(1, 0, "state", false),
		{Site: OperationSite{Block: 2, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 1 || report.Replacements[0].Kind != RegionLoadFromPhi || report.Replacements[0].Result != 4 || report.Replacements[0].Replacement != 6 {
		t.Fatalf("loop memory-phi report = %+v", report.Replacements)
	}
	if len(result.Blocks[1].Parameters) != 1 || result.Blocks[1].Parameters[0].ID != 6 || len(result.Blocks[1].Operations) != 0 ||
		!reflect.DeepEqual(result.Blocks[1].Terminator.False.Arguments, []ValueID{6}) {
		t.Fatalf("loop memory-phi header = %+v", result.Blocks[1])
	}
	if !reflect.DeepEqual(result.Blocks[0].Terminator.True.Arguments, []ValueID{2}) ||
		!reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{3}) || len(resultMetadata.Operations) != 2 {
		t.Fatalf("loop memory-phi edges = entry %v backedge %v, metadata %+v", result.Blocks[0].Terminator.True.Arguments, result.Blocks[2].Terminator.True.Arguments, resultMetadata)
	}
}

func TestRegionLoadForwardingPromotesLoadsDominatedByLoopPhi(t *testing.T) {
	cfg := CFG{
		Name: "loop_dominated_loads", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{
				ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}},
				Operations: []Operation{regionLoadOperation(2, "u32")},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}},
			},
			{ID: 1, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 2}, False: Edge{Target: 3}}},
			{
				ID: 2,
				Operations: []Operation{
					regionLoadOperation(3, "u32"),
					{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}},
				},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1}},
			},
			{ID: 3, Operations: []Operation{regionLoadOperation(4, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		regionLoadMetadata(0, 0, "state", false),
		regionLoadMetadata(2, 0, "state", false),
		{Site: OperationSite{Block: 2, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
		regionLoadMetadata(3, 0, "state", false),
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 2 || report.Replacements[0].Kind != RegionLoadFromPhi || report.Replacements[0].Result != 3 || report.Replacements[0].Replacement != 5 ||
		report.Replacements[1].Kind != RegionLoadFromPhi || report.Replacements[1].Result != 4 || report.Replacements[1].Replacement != 5 {
		t.Fatalf("dominated loop-load report = %+v", report.Replacements)
	}
	if len(result.Blocks[1].Parameters) != 1 || result.Blocks[1].Parameters[0].ID != 5 ||
		!reflect.DeepEqual(result.Blocks[0].Terminator.True.Arguments, []ValueID{2}) ||
		!reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{5}) {
		t.Fatalf("dominated loop-load phi = header %+v, entry %v, backedge %v", result.Blocks[1], result.Blocks[0].Terminator.True.Arguments, result.Blocks[2].Terminator.True.Arguments)
	}
	if len(result.Blocks[2].Operations) != 1 || !reflect.DeepEqual(result.Blocks[2].Operations[0].Operands, []ValueID{5}) || len(result.Blocks[3].Operations) != 0 ||
		!reflect.DeepEqual(result.Blocks[3].Terminator.Values, []ValueID{5}) || len(resultMetadata.Operations) != 2 {
		t.Fatalf("dominated loop-load output = CFG %+v, metadata %+v", result, resultMetadata)
	}
}

func TestRegionLoadForwardingRefusesConceptualEntryLoopPhi(t *testing.T) {
	cfg := CFG{
		Name: "entry_loop", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{
				ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}},
				Operations: []Operation{regionLoadOperation(3, "u32")},
				Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2, Arguments: []ValueID{3}}},
			},
			{
				ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}},
				Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 0, Arguments: []ValueID{1, 2}}},
			},
			{ID: 2, Parameters: []Value{{ID: 4, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
		},
	}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
		regionLoadMetadata(0, 0, "state", false),
		{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}},
	}}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if report.Changes() != 0 || !sameDeadStoreCFG(result, cfg) || !sameDeadStoreMetadata(t, cfg, metadata, result, resultMetadata) {
		t.Fatalf("conceptual entry memory phi changed: report %+v, CFG %+v, metadata %+v", report, result, resultMetadata)
	}
}

func TestRegionLoadForwardingMaterializesOneSafeJoinInputAndKeepsRefusals(t *testing.T) {
	t.Run("unconditional entry edge", func(t *testing.T) {
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
		if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, report); err != nil {
			t.Fatal(err)
		}
		wantInsertion := RegionLoadInsertion{
			Site: OperationSite{Block: 2, Index: 0}, Target: 3, Region: "state", Memory: 1,
			Result: 4, TemplateAccess: 2,
		}
		if report.Changes() != 2 || len(report.Replacements) != 1 || report.Replacements[0].Kind != RegionLoadFromPhi ||
			!reflect.DeepEqual(report.Insertions, []RegionLoadInsertion{wantInsertion}) {
			t.Fatalf("materialized join report=%+v", report)
		}
		if len(result.Blocks[2].Operations) != 1 || result.Blocks[2].Operations[0].Results[0].ID != 4 ||
			!reflect.DeepEqual(result.Blocks[2].Terminator.True.Arguments, []ValueID{4}) ||
			len(result.Blocks[3].Parameters) != 1 || result.Blocks[3].Parameters[0].ID != 5 ||
			!reflect.DeepEqual(result.Blocks[3].Terminator.Values, []ValueID{5}) {
			t.Fatalf("materialized join CFG=%+v", result)
		}
		if len(resultMetadata.Operations) != 2 || resultMetadata.Operations[1].Site != (OperationSite{Block: 2, Index: 0}) ||
			resultMetadata.Operations[1].Accesses[0] != (MemoryAccessSpec{Region: "state", Kind: MemoryRead}) {
			t.Fatalf("materialized join metadata=%+v", resultMetadata)
		}
		mutated := report
		mutated.Insertions = append([]RegionLoadInsertion(nil), report.Insertions...)
		mutated.Insertions[0].Target = 99
		if err := VerifyRegionLoadForwarding(cfg, metadata, memorySSA, result, resultMetadata, mutated); err == nil || !strings.Contains(err.Error(), "was mutated") {
			t.Fatalf("mutated insertion verification = %v", err)
		}
	})

	t.Run("conditional critical edge", func(t *testing.T) {
		cfg := CFG{
			Name: "join_critical_edge", Entry: 0, Results: []Type{"u32"},
			Blocks: []Block{
				{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 3}}},
				{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
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
		if report.Changes() != 0 || !sameDeadStoreCFG(result, cfg) || !sameDeadStoreMetadata(t, cfg, metadata, result, resultMetadata) {
			t.Fatalf("critical-edge load was materialized: report=%+v CFG=%+v metadata=%+v", report, result, resultMetadata)
		}
	})

	t.Run("two unavailable edges", func(t *testing.T) {
		cfg := CFG{
			Name: "join_two_missing", Entry: 0, Results: []Type{"u32"},
			Blocks: []Block{
				{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
				{ID: 1, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
				{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
				{ID: 3, Operations: []Operation{regionLoadOperation(2, "u32")}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
			},
		}
		metadata := RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{regionLoadMetadata(3, 0, "state", false)}}
		memorySSA := mustRegionLoadMemorySSA(t, cfg, metadata)
		result, resultMetadata, report, err := ForwardRegionLoads(cfg, metadata, memorySSA)
		if err != nil {
			t.Fatal(err)
		}
		if report.Changes() != 0 || !sameDeadStoreCFG(result, cfg) || !sameDeadStoreMetadata(t, cfg, metadata, result, resultMetadata) {
			t.Fatalf("two missing loads were materialized: report=%+v CFG=%+v metadata=%+v", report, result, resultMetadata)
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

func TestRegionLoadForwardingMovesCheckedLoadAuthorityToMaterializedEdge(t *testing.T) {
	read := checkedMemoryRecord(t, Source{Context: "edge.oak", Line: 8, Column: 3}, "state", MemoryRead, "u32", false)
	write := checkedMemoryRecord(t, Source{Context: "edge.oak", Line: 4, Column: 5}, "state", MemoryWrite, "u32", true)
	authority, err := NewCheckedMemoryAuthority([]CheckedMemoryAccessRecord{read, write})
	if err != nil {
		t.Fatal(err)
	}
	cfg := CFG{
		Name: "checked_join_edge", Entry: 0, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 0, Parameters: []Value{{ID: 1, Type: TypeBool}, {ID: 2, Type: "u32"}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 1}, False: Edge{Target: 2}}},
			{ID: 1, Operations: []Operation{{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}, Source: write.Source, MemoryAccessID: write.ID}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 2, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 3}}},
			{ID: 3, Operations: []Operation{{Code: OpLoadRegion, Results: []Value{{ID: 3, Type: "u32", Source: read.Source}}, Effects: []Effect{EffectReadMemory}, Source: read.Source, MemoryAccessID: read.ID}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		t.Fatal(err)
	}
	memorySSA := mustRegionLoadMemorySSA(t, cfg, projection.Metadata)
	result, resultMetadata, report, err := ForwardRegionLoads(cfg, projection.Metadata, memorySSA)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionLoadForwarding(cfg, projection.Metadata, memorySSA, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	finalProjection, err := ProjectCheckedMemory(result, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(result, authority, finalProjection); err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(finalProjection.Metadata, resultMetadata) {
		t.Fatalf("checked materialized metadata = %+v, want %+v", finalProjection.Metadata, resultMetadata)
	}
	inserted := result.Blocks[2].Operations
	if len(inserted) != 1 || inserted[0].MemoryAccessID != read.ID || inserted[0].Source != read.Source ||
		len(report.Insertions) != 1 || report.Insertions[0].TemplateAccess != 2 {
		t.Fatalf("checked materialized load = %+v, report %+v", inserted, report)
	}
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
