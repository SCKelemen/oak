package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestRegionMemorySSAStraightLineReadWrite(t *testing.T) {
	cfg := memoryStraightLineCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryRead}}},
			{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryWrite}}},
		},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, metadata, analysis); err != nil {
		t.Fatal(err)
	}
	wantAccesses := []MemoryAccess{
		{ID: 1, Site: OperationSite{Block: 1, Index: 0}, Region: "heap", Kind: MemoryRead, Input: 1},
		{ID: 2, Site: OperationSite{Block: 1, Index: 1}, Region: "heap", Kind: MemoryWrite, Input: 1, Output: 2},
	}
	wantVersions := []MemoryVersion{
		{ID: 1, Region: "heap", Kind: MemoryVersionEntry, Block: 1},
		{ID: 2, Region: "heap", Kind: MemoryVersionDefinition, Block: 1, Definition: 2},
	}
	if !reflect.DeepEqual(analysis.Accesses, wantAccesses) || !reflect.DeepEqual(analysis.Versions, wantVersions) {
		t.Fatalf("memory SSA = accesses %+v versions %+v", analysis.Accesses, analysis.Versions)
	}
}

func TestRegionMemorySSAKeepsDisjointRegionsIndependent(t *testing.T) {
	cfg := CFG{
		Name: "disjoint", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 1,
			Operations: []Operation{
				{Code: "memory.store", Effects: []Effect{EffectWriteMemory}},
				{Code: "memory.load", Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"right", "left"},
		Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "right", Kind: MemoryRead}}},
			{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "left", Kind: MemoryWrite}}},
		},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if got := analysis.Regions; !reflect.DeepEqual(got, []RegionID{"left", "right"}) {
		t.Fatalf("canonical regions = %v", got)
	}
	if analysis.Accesses[0].Region != "left" || analysis.Accesses[0].Input != 1 || analysis.Accesses[0].Output != 3 {
		t.Fatalf("left write = %+v", analysis.Accesses[0])
	}
	if analysis.Accesses[1].Region != "right" || analysis.Accesses[1].Input != 2 || analysis.Accesses[1].Output != 0 {
		t.Fatalf("right read was coupled to left write: %+v", analysis.Accesses[1])
	}

	reordered := metadata
	reordered.Regions = []RegionID{"left", "right"}
	reordered.Operations = []MemoryOperationMetadata{metadata.Operations[1], metadata.Operations[0]}
	again, err := AnalyzeRegionMemorySSA(cfg, reordered)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, reordered, analysis); err != nil {
		t.Fatalf("canonical metadata order did not preserve evidence identity: %v", err)
	}
	if !reflect.DeepEqual(analysis.Regions, again.Regions) || !reflect.DeepEqual(analysis.Accesses, again.Accesses) || !reflect.DeepEqual(analysis.Versions, again.Versions) {
		t.Fatalf("metadata declaration order changed memory SSA: first=%+v again=%+v", analysis, again)
	}
}

func TestRegionMemorySSADiamondCreatesJoinPhi(t *testing.T) {
	cfg := memoryDiamondCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 2, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryWrite}}},
			{Site: OperationSite{Block: 4, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryRead}}},
		},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, metadata, analysis); err != nil {
		t.Fatal(err)
	}
	phi := memoryVersionOfKind(t, analysis, MemoryVersionPhi, "heap", 4)
	wantIncoming := []MemoryIncoming{{Predecessor: 2, Version: 3}, {Predecessor: 3, Version: 1}}
	if phi.ID != 2 || !reflect.DeepEqual(phi.Incoming, wantIncoming) {
		t.Fatalf("diamond phi = %+v, want incoming %+v", phi, wantIncoming)
	}
	if read := analysis.Accesses[1]; read.Input != phi.ID || read.Kind != MemoryRead {
		t.Fatalf("join read = %+v, phi = %+v", read, phi)
	}
}

func TestRegionMemorySSALoopCreatesHeaderPhi(t *testing.T) {
	cfg := memoryLoopCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"state"},
		Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 3, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryReadWrite}}},
			{Site: OperationSite{Block: 4, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryRead}}},
		},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, metadata, analysis); err != nil {
		t.Fatal(err)
	}
	phi := memoryVersionOfKind(t, analysis, MemoryVersionPhi, "state", 2)
	wantIncoming := []MemoryIncoming{{Predecessor: 1, Version: 1}, {Predecessor: 3, Version: 3}}
	if phi.ID != 2 || !reflect.DeepEqual(phi.Incoming, wantIncoming) {
		t.Fatalf("loop phi = %+v, want incoming %+v", phi, wantIncoming)
	}
	if body := analysis.Accesses[0]; body.Input != phi.ID || body.Output != 3 || body.Kind != MemoryReadWrite {
		t.Fatalf("loop body access = %+v", body)
	}
	if exit := analysis.Accesses[1]; exit.Input != phi.ID {
		t.Fatalf("loop exit read = %+v, want header phi %d", exit, phi.ID)
	}
}

func TestRegionMemorySSAUnknownCallClobbersEveryRegion(t *testing.T) {
	cfg := CFG{
		Name: "opaque_call", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 1,
			Operations: []Operation{
				{Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"a", "b"},
		Operations: []MemoryOperationMetadata{{
			Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Kind: MemoryUnknownClobber}},
		}},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	want := []MemoryAccess{
		{ID: 1, Site: OperationSite{Block: 1, Index: 0}, Region: "a", Kind: MemoryUnknownClobber, Input: 1, Output: 3},
		{ID: 2, Site: OperationSite{Block: 1, Index: 0}, Region: "b", Kind: MemoryUnknownClobber, Input: 2, Output: 4},
	}
	if !reflect.DeepEqual(analysis.Accesses, want) {
		t.Fatalf("unknown call accesses = %+v, want %+v", analysis.Accesses, want)
	}
}

func TestRegionMemorySSANoModRefCallCreatesNoAccess(t *testing.T) {
	cfg := CFG{Name: "pure_call", Entry: 1, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 1, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}},
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	metadata := RegionMemoryMetadata{Operations: []MemoryOperationMetadata{{
		Site: OperationSite{Block: 1, Index: 0}, CallEffect: MemoryCallNoModRef,
	}}}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyRegionMemorySSA(cfg, metadata, analysis); err != nil {
		t.Fatal(err)
	}
	if len(analysis.Accesses) != 0 || len(analysis.Versions) != 0 {
		t.Fatalf("no-ModRef call changed memory SSA: %+v", analysis)
	}

	tests := []struct {
		name     string
		metadata RegionMemoryMetadata
		want     string
	}{
		{name: "missing", metadata: RegionMemoryMetadata{}, want: "unknown-clobber"},
		{name: "unknown", metadata: RegionMemoryMetadata{Operations: []MemoryOperationMetadata{{Site: OperationSite{Block: 1, Index: 0}, CallEffect: "forged"}}}, want: "unknown call effect"},
		{name: "with access", metadata: RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{{Site: OperationSite{Block: 1, Index: 0}, CallEffect: MemoryCallNoModRef, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryRead}}}}}, want: "cannot carry accesses"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if _, err := AnalyzeRegionMemorySSA(cfg, test.metadata); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}
	malformedCall := cloneCFG(cfg)
	malformedCall.Blocks[0].Operations[0].Attributes = nil
	if _, err := AnalyzeRegionMemorySSA(malformedCall, metadata); err == nil || !strings.Contains(err.Error(), "callee attribute") {
		t.Fatalf("malformed summarized call error = %v", err)
	}
}

func TestRegionMemorySSARefCallReadsExactRegions(t *testing.T) {
	cfg := CFG{Name: "read_call", Entry: 1, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 1, Operations: []Operation{{
			Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall},
			Attributes: []Attribute{{Name: AttributeCallee, Value: "read"}},
		}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
	}}}
	metadata := RegionMemoryMetadata{Regions: []RegionID{"left", "right"}, Operations: []MemoryOperationMetadata{{
		Site: OperationSite{Block: 1, Index: 0}, CallEffect: MemoryCallRef,
		Accesses: []MemoryAccessSpec{{Region: "right", Kind: MemoryRead}, {Region: "left", Kind: MemoryRead}},
	}}}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	want := []MemoryAccess{
		{ID: 1, Site: OperationSite{Block: 1, Index: 0}, Region: "left", Kind: MemoryRead, Input: 1},
		{ID: 2, Site: OperationSite{Block: 1, Index: 0}, Region: "right", Kind: MemoryRead, Input: 2},
	}
	if !reflect.DeepEqual(analysis.Accesses, want) {
		t.Fatalf("Ref call accesses = %+v, want %+v", analysis.Accesses, want)
	}
	reordered := metadata
	reordered.Operations = append([]MemoryOperationMetadata(nil), metadata.Operations...)
	reordered.Operations[0].Accesses = []MemoryAccessSpec{{Region: "left", Kind: MemoryRead}, {Region: "right", Kind: MemoryRead}}
	if err := VerifyRegionMemorySSA(cfg, reordered, analysis); err != nil {
		t.Fatalf("canonical access order changed evidence: %v", err)
	}
	mutated := metadata
	mutated.Operations = append([]MemoryOperationMetadata(nil), metadata.Operations...)
	mutated.Operations[0].Accesses = []MemoryAccessSpec{{Region: "left", Kind: MemoryRead}}
	if err := VerifyRegionMemorySSA(cfg, mutated, analysis); err == nil || !strings.Contains(err.Error(), "different metadata") {
		t.Fatalf("changed Ref set verification error = %v", err)
	}

	invalid := []struct {
		name   string
		access []MemoryAccessSpec
		want   string
	}{
		{name: "empty", want: "has no accesses"},
		{name: "write", access: []MemoryAccessSpec{{Region: "left", Kind: MemoryWrite, WholeRegion: true}}, want: "exact nonvolatile reads"},
		{name: "read-write", access: []MemoryAccessSpec{{Region: "left", Kind: MemoryReadWrite}}, want: "exact nonvolatile reads"},
		{name: "volatile", access: []MemoryAccessSpec{{Region: "left", Kind: MemoryRead, Volatile: true}}, want: "exact nonvolatile reads"},
	}
	for _, test := range invalid {
		t.Run(test.name, func(t *testing.T) {
			candidate := RegionMemoryMetadata{Regions: []RegionID{"left"}, Operations: []MemoryOperationMetadata{{
				Site: OperationSite{Block: 1, Index: 0}, CallEffect: MemoryCallRef, Accesses: test.access,
			}}}
			if _, err := AnalyzeRegionMemorySSA(cfg, candidate); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want %q", err, test.want)
			}
		})
	}
}

func TestRegionMemorySSAFailsClosedOnMissingOrMalformedMetadata(t *testing.T) {
	cfg := memoryStraightLineCFG()
	tests := []struct {
		name     string
		metadata RegionMemoryMetadata
		want     string
	}{
		{name: "missing", metadata: RegionMemoryMetadata{Regions: []RegionID{"heap"}}, want: "has no region metadata"},
		{name: "undeclared", metadata: RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "other", Kind: MemoryRead}}}}}, want: "undeclared region"},
		{name: "wrong modref", metadata: RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryWrite}}}, {Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryWrite}}}}}, want: "ModRef does not match"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if _, err := AnalyzeRegionMemorySSA(cfg, test.metadata); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("error = %v, want substring %q", err, test.want)
			}
		})
	}

	unknown := CFG{
		Name: "unknown", Entry: 1,
		Blocks: []Block{{ID: 1, Operations: []Operation{{Code: "extension.unknown"}}, Terminator: Terminator{Kind: TerminatorReturn}}},
	}
	if _, err := AnalyzeRegionMemorySSA(unknown, RegionMemoryMetadata{}); err == nil || !strings.Contains(err.Error(), "unknown-clobber") {
		t.Fatalf("unknown operation without metadata error = %v", err)
	}
}

func TestRegionMemorySSAVerifierRejectsStaleAndMutatedEvidence(t *testing.T) {
	cfg := memoryStraightLineCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			{Site: OperationSite{Block: 1, Index: 0}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryRead}}},
			{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Region: "heap", Kind: MemoryWrite}}},
		},
	}
	analysis, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}

	staleCFG := cfg
	staleCFG.Blocks = append([]Block(nil), cfg.Blocks...)
	staleCFG.Blocks[0].Operations = append([]Operation(nil), cfg.Blocks[0].Operations...)
	staleCFG.Blocks[0].Operations[0].Source.Line = 99
	if err := VerifyRegionMemorySSA(staleCFG, metadata, analysis); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("stale CFG error = %v", err)
	}

	staleMetadata := metadata
	staleMetadata.Regions = []RegionID{"heap", "other"}
	if err := VerifyRegionMemorySSA(cfg, staleMetadata, analysis); err == nil || !strings.Contains(err.Error(), "different metadata") {
		t.Fatalf("stale metadata error = %v", err)
	}

	mutated := analysis
	mutated.Accesses = append([]MemoryAccess(nil), analysis.Accesses...)
	mutated.Accesses[0].Input = 99
	if err := VerifyRegionMemorySSA(cfg, metadata, mutated); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("mutated analysis error = %v", err)
	}
}

func memoryStraightLineCFG() CFG {
	return CFG{
		Name: "straight", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{{
			ID: 1,
			Operations: []Operation{
				{Code: "memory.load", Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectReadMemory}},
				{Code: "memory.store", Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
			},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{1}},
		}},
	}
}

func memoryDiamondCFG() CFG {
	return CFG{
		Name: "diamond", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 1, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 1, True: Edge{Target: 2}, False: Edge{Target: 3}}},
			{ID: 2, Operations: []Operation{{Code: "memory.store", Effects: []Effect{EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 4}}},
			{ID: 3, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 4}}},
			{ID: 4, Operations: []Operation{{Code: "memory.load", Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectReadMemory}}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}}},
		},
	}
}

func memoryLoopCFG() CFG {
	return CFG{
		Name: "loop", Entry: 1, Results: []Type{"u32"},
		Blocks: []Block{
			{ID: 1, Parameters: []Value{{ID: 1, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 2, Arguments: []ValueID{1}}}},
			{ID: 2, Parameters: []Value{{ID: 2, Type: TypeBool}}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 2, True: Edge{Target: 3}, False: Edge{Target: 4}}},
			{ID: 3, Operations: []Operation{{Code: "memory.update", Effects: []Effect{EffectReadMemory, EffectWriteMemory}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 2, Arguments: []ValueID{2}}}},
			{ID: 4, Operations: []Operation{{Code: "memory.load", Results: []Value{{ID: 3, Type: "u32"}}, Effects: []Effect{EffectReadMemory}}}, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}}},
		},
	}
}

func memoryVersionOfKind(t *testing.T, analysis RegionMemorySSA, kind MemoryVersionKind, region RegionID, block BlockID) MemoryVersion {
	t.Helper()
	for _, version := range analysis.Versions {
		if version.Kind == kind && version.Region == region && version.Block == block {
			return version
		}
	}
	t.Fatalf("missing memory version kind=%s region=%s block=%d in %+v", kind, region, block, analysis.Versions)
	return MemoryVersion{}
}
