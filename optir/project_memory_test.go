package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestProjectWithCheckedMemoryNestedSites(t *testing.T) {
	var records []CheckedMemoryAccessRecord
	var stores []*Operation
	for i := 0; i < 3; i++ {
		record := checkedMemoryRecord(t, Source{Context: "nested.oak", Line: i + 1, Column: 1}, "global:state", MemoryWrite, "u32", true)
		records = append(records, record)
		stores = append(stores, &Operation{Code: OpStoreRegion, Operands: []ValueID{3}, Effects: []Effect{EffectWriteMemory}, Source: record.Source, MemoryAccessID: record.ID})
	}
	read := checkedMemoryRecord(t, Source{Context: "nested.oak", Line: 4, Column: 1}, "global:state", MemoryRead, "u32", false)
	records = append(records, read)
	load := &Operation{Code: OpLoadRegion, Results: []Value{value(6, "u32", "loaded")}, Effects: []Effect{EffectReadMemory}, Source: read.Source, MemoryAccessID: read.ID}
	arm := func(store *Operation) Region { return Region{Nodes: []Node{{Operation: store}}, Yield: []ValueID{3}} }
	inner := &If{Condition: 2, Results: []Value{value(4, "u32", "inner")}, Then: arm(stores[0]), Else: arm(stores[1])}
	outer := &If{Condition: 1, Results: []Value{value(5, "u32", "outer")},
		Then: Region{Nodes: []Node{{If: inner}}, Yield: []ValueID{4}}, Else: arm(stores[2])}
	function := Function{Name: "nested", Parameters: []Value{value(1, TypeBool, "p"), value(2, TypeBool, "q"), value(3, "u32", "v")}, Results: []Type{"u32"},
		Body: Region{Nodes: []Node{{If: outer}, {Operation: load}}, Yield: []ValueID{6}}}
	authority, err := NewCheckedMemoryAuthority(records)
	if err != nil {
		t.Fatal(err)
	}
	cfg, projection, err := ProjectWithCheckedMemory(function, authority)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyCheckedMemoryProjection(cfg, authority, projection); err != nil {
		t.Fatal(err)
	}
	// DFS visits the inner stores (blocks 4,5), outer else (2), then tail (3).
	// Metadata must use CFG site order without moving any actual operation.
	want := []struct {
		block  BlockID
		record CheckedMemoryAccessRecord
	}{{2, records[2]}, {3, read}, {4, records[0]}, {5, records[1]}}
	if len(projection.Metadata.Operations) != len(want) {
		t.Fatal("lost memory site")
	}
	for i, w := range want {
		metadata := projection.Metadata.Operations[i]
		op := cfg.Blocks[w.block].Operations[0]
		if metadata.Site != (OperationSite{Block: w.block, Index: 0}) || len(metadata.Accesses) != 1 || metadata.Accesses[0].Kind != w.record.Kind || op.MemoryAccessID != w.record.ID || op.Source != w.record.Source {
			t.Fatalf("memory binding moved: %+v / %+v", metadata, op)
		}
	}
	cfg.Blocks[4].Operations[0].MemoryAccessID = records[1].ID
	if _, err := ProjectCheckedMemory(cfg, authority); err == nil {
		t.Fatal("normalization licensed forged site identity")
	}
}

func TestProjectWithRegionMemoryTracksExactStructuredOperations(t *testing.T) {
	thenStore := &Operation{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}
	elseStore := &Operation{Code: OpStoreRegion, Operands: []ValueID{2}, Effects: []Effect{EffectWriteMemory}}
	function := Function{
		Name: "choose_store", Parameters: []Value{value(1, TypeBool, "condition"), value(2, "u32", "value")}, Results: []Type{"u32"},
		Body: Region{
			Nodes: []Node{{If: &If{
				Condition: 1, Results: []Value{value(3, "u32", "selected")},
				Then: Region{Nodes: []Node{{Operation: thenStore}}, Yield: []ValueID{2}},
				Else: Region{Nodes: []Node{{Operation: elseStore}}, Yield: []ValueID{2}},
			}}},
			Yield: []ValueID{3},
		},
	}
	access := func(operation *Operation) StructuredMemoryOperationMetadata {
		return StructuredMemoryOperationMetadata{Operation: operation, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}}
	}
	cfg, metadata, err := ProjectWithRegionMemory(function, StructuredRegionMemoryMetadata{
		Regions: []RegionID{"state"}, Operations: []StructuredMemoryOperationMetadata{access(thenStore), access(elseStore)},
	})
	if err != nil {
		t.Fatal(err)
	}
	wantSites := []OperationSite{{Block: 1, Index: 0}, {Block: 2, Index: 0}}
	gotSites := []OperationSite{metadata.Operations[0].Site, metadata.Operations[1].Site}
	if !reflect.DeepEqual(gotSites, wantSites) {
		t.Fatalf("projected memory sites = %v, want %v", gotSites, wantSites)
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, metadata, analysis); err != nil {
		t.Fatal(err)
	}
}

func TestProjectWithRegionMemoryFeedsVerifiedDeadStoreElimination(t *testing.T) {
	first := &Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}
	second := &Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}
	function := Function{
		Name: "overwrite", Parameters: []Value{value(1, "u32", "value")}, Results: []Type{"u32"},
		Body: Region{Nodes: []Node{{Operation: first}, {Operation: second}}, Yield: []ValueID{1}},
	}
	access := func(operation *Operation) StructuredMemoryOperationMetadata {
		return StructuredMemoryOperationMetadata{Operation: operation, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}}
	}
	structured := StructuredRegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []StructuredMemoryOperationMetadata{access(first), access(second)}}
	cfg, metadata, err := ProjectWithRegionMemory(function, structured)
	if err != nil {
		t.Fatal(err)
	}
	ssa, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	observability := RegionMemoryObservability{LiveOut: []RegionID{"state"}}
	liveness, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, ssa, observability)
	if err != nil {
		t.Fatal(err)
	}
	result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, ssa, observability, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyDeadStoreElimination(cfg, metadata, ssa, observability, liveness, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if len(report.Removed) != 1 || report.Removed[0].Site != (OperationSite{Block: 0, Index: 0}) {
		t.Fatalf("removed stores = %+v, want first store", report.Removed)
	}
	if len(result.Blocks[0].Operations) != 1 || resultMetadata.Operations[0].Site != (OperationSite{Block: 0, Index: 0}) {
		t.Fatalf("DSE result or metadata was not renumbered: cfg=%+v metadata=%+v", result, resultMetadata)
	}
}

func TestProjectWithRegionMemoryRejectsInvalidOperationIdentity(t *testing.T) {
	store := &Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}
	foreign := &Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}
	function := Function{Name: "store", Parameters: []Value{value(1, "u32", "value")}, Results: []Type{"u32"}, Body: Region{Nodes: []Node{{Operation: store}}, Yield: []ValueID{1}}}
	spec := func(operation *Operation) StructuredMemoryOperationMetadata {
		return StructuredMemoryOperationMetadata{Operation: operation, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}}
	}
	tests := []struct {
		name string
		ops  []StructuredMemoryOperationMetadata
		want string
	}{
		{name: "nil", ops: []StructuredMemoryOperationMetadata{{}}, want: "nil operation"},
		{name: "foreign", ops: []StructuredMemoryOperationMetadata{spec(foreign)}, want: "outside the function"},
		{name: "duplicate", ops: []StructuredMemoryOperationMetadata{spec(store), spec(store)}, want: "repeats an operation"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			_, _, err := ProjectWithRegionMemory(function, StructuredRegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: test.ops})
			if err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("invalid structured memory identity error = %v, want %q", err, test.want)
			}
		})
	}

	reused := function
	reused.Body.Nodes = append(reused.Body.Nodes, Node{Operation: store})
	if _, _, err := ProjectWithRegionMemory(reused, StructuredRegionMemoryMetadata{
		Regions: []RegionID{"state"}, Operations: []StructuredMemoryOperationMetadata{spec(store)},
	}); err == nil || !strings.Contains(err.Error(), "occurs more than once") {
		t.Fatalf("reused structured operation error = %v", err)
	}

	if _, _, err := ProjectWithRegionMemory(function, StructuredRegionMemoryMetadata{Regions: []RegionID{"state"}}); err == nil || !strings.Contains(err.Error(), "memory effect has no region metadata") {
		t.Fatalf("missing memory metadata error = %v", err)
	}
}

func TestProjectWithRegionMemoryCopiesAccessMetadata(t *testing.T) {
	store := &Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}
	function := Function{Name: "store", Parameters: []Value{value(1, "u32", "value")}, Results: []Type{"u32"}, Body: Region{Nodes: []Node{{Operation: store}}, Yield: []ValueID{1}}}
	accesses := []MemoryAccessSpec{{Region: "state", Kind: MemoryWrite, WholeRegion: true}}
	_, metadata, err := ProjectWithRegionMemory(function, StructuredRegionMemoryMetadata{
		Regions: []RegionID{"state"}, Operations: []StructuredMemoryOperationMetadata{{Operation: store, Accesses: accesses}},
	})
	if err != nil {
		t.Fatal(err)
	}
	accesses[0].Region = "mutated"
	if metadata.Operations[0].Accesses[0].Region != "state" {
		t.Fatalf("projected access metadata aliases caller input: %+v", metadata)
	}
}

func TestProjectKeepsOpaqueCallCompatibility(t *testing.T) {
	call := &Operation{Code: OpCall, Results: []Value{value(2, "u32", "result")}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "callee"}}}
	function := Function{Name: "caller", Parameters: []Value{value(1, "u32", "value")}, Results: []Type{"u32"}, Body: Region{Nodes: []Node{{Operation: call}}, Yield: []ValueID{2}}}
	if _, err := Project(function); err != nil {
		t.Fatalf("ordinary projection unexpectedly required region metadata: %v", err)
	}
	if _, _, err := ProjectWithRegionMemory(function, StructuredRegionMemoryMetadata{}); err == nil || !strings.Contains(err.Error(), "unknown-clobber") {
		t.Fatalf("memory-aware projection accepted opaque call without metadata: %v", err)
	}
}
