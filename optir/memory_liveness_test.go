package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestMemoryDefinitionLivenessFindsOverwrittenDefinition(t *testing.T) {
	cfg := memoryLivenessLinearCFG("overwrite", []Effect{
		EffectWriteMemory,
		EffectWriteMemory,
		EffectReadMemory,
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "heap", MemoryWrite),
			memoryMetadata(1, 1, "heap", MemoryWrite),
			memoryMetadata(1, 2, "heap", MemoryRead),
		},
	}
	analysis := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{})
	if got, want := analysis.LiveAccesses, []MemoryAccessID{2, 3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("live accesses = %v, want %v", got, want)
	}
	if got, want := analysis.LiveVersions, []MemoryVersionID{3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("live versions = %v, want %v", got, want)
	}
	if got, want := analysis.DeadAccessCandidates, []MemoryAccessID{1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("dead access candidates = %v, want %v", got, want)
	}
	if got, want := analysis.DeadVersionCandidates, []MemoryVersionID{2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("dead version candidates = %v, want %v", got, want)
	}
}

func TestMemoryDefinitionLivenessReadKeepsReachingDefinition(t *testing.T) {
	cfg := memoryLivenessLinearCFG("read", []Effect{EffectWriteMemory, EffectReadMemory})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "heap", MemoryWrite),
			memoryMetadata(1, 1, "heap", MemoryRead),
		},
	}
	analysis := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{})
	if len(analysis.DeadAccessCandidates) != 0 || len(analysis.DeadVersionCandidates) != 0 {
		t.Fatalf("read left dead candidates: %+v", analysis)
	}
	if got, want := analysis.LiveAccesses, []MemoryAccessID{1, 2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("live accesses = %v, want %v", got, want)
	}
}

func TestMemoryDefinitionLivenessRequiresExplicitLiveOut(t *testing.T) {
	cfg := memoryLivenessLinearCFG("live_out", []Effect{EffectWriteMemory, EffectWriteMemory})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "heap", MemoryWrite),
			memoryMetadata(1, 1, "heap", MemoryWrite),
		},
	}
	without := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{})
	if got, want := without.DeadAccessCandidates, []MemoryAccessID{1, 2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("implicit live-out candidates = %v, want %v", got, want)
	}
	with := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{LiveOut: []RegionID{"heap"}})
	if got, want := with.DeadAccessCandidates, []MemoryAccessID{1}; !reflect.DeepEqual(got, want) {
		t.Fatalf("explicit live-out candidates = %v, want %v", got, want)
	}
	if got, want := with.LiveVersions, []MemoryVersionID{3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("explicit live-out versions = %v, want %v", got, want)
	}
	if _, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, mustMemorySSA(t, cfg, metadata), RegionMemoryObservability{LiveOut: []RegionID{"missing"}}); err == nil || !strings.Contains(err.Error(), "undeclared region") {
		t.Fatalf("undeclared live-out error = %v", err)
	}
}

func TestMemoryDefinitionLivenessKeepsRegionsDisjoint(t *testing.T) {
	cfg := memoryLivenessLinearCFG("disjoint", []Effect{EffectWriteMemory, EffectWriteMemory, EffectReadMemory})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"b", "a"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "a", MemoryWrite),
			memoryMetadata(1, 1, "b", MemoryWrite),
			memoryMetadata(1, 2, "a", MemoryRead),
		},
	}
	analysis := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{})
	if got, want := analysis.DeadAccessCandidates, []MemoryAccessID{2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("disjoint dead candidates = %v, want %v", got, want)
	}
	if got, want := analysis.DeadVersionCandidates, []MemoryVersionID{4}; !reflect.DeepEqual(got, want) {
		t.Fatalf("disjoint dead versions = %v, want %v", got, want)
	}
}

func TestMemoryDefinitionLivenessPropagatesThroughDiamondPhi(t *testing.T) {
	cfg := memoryDiamondCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(2, 0, "heap", MemoryWrite),
			memoryMetadata(4, 0, "heap", MemoryRead),
		},
	}
	memorySSA := mustMemorySSA(t, cfg, metadata)
	analysis, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, memorySSA, RegionMemoryObservability{})
	if err != nil {
		t.Fatal(err)
	}
	phi := memoryVersionOfKind(t, memorySSA, MemoryVersionPhi, "heap", 4)
	if !containsMemoryVersion(analysis.LiveVersions, phi.ID) || !containsMemoryVersion(analysis.LiveVersions, 3) || !containsMemoryVersion(analysis.LiveVersions, 1) {
		t.Fatalf("diamond phi inputs are not live: %+v", analysis)
	}
	if len(analysis.DeadAccessCandidates) != 0 {
		t.Fatalf("diamond write was reported dead: %+v", analysis)
	}
}

func TestMemoryDefinitionLivenessPropagatesThroughLoopPhi(t *testing.T) {
	cfg := memoryLoopCFG()
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"state"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(3, 0, "state", MemoryReadWrite),
			memoryMetadata(4, 0, "state", MemoryRead),
		},
	}
	memorySSA := mustMemorySSA(t, cfg, metadata)
	analysis, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, memorySSA, RegionMemoryObservability{})
	if err != nil {
		t.Fatal(err)
	}
	phi := memoryVersionOfKind(t, memorySSA, MemoryVersionPhi, "state", 2)
	if !containsMemoryVersion(analysis.LiveVersions, phi.ID) || !containsMemoryVersion(analysis.LiveVersions, 1) || !containsMemoryVersion(analysis.LiveVersions, 3) {
		t.Fatalf("loop phi web is not live: %+v", analysis)
	}
	if len(analysis.DeadAccessCandidates) != 0 {
		t.Fatalf("loop reported dead exact writes: %+v", analysis)
	}
}

func TestMemoryDefinitionLivenessTreatsOpaqueCallConservatively(t *testing.T) {
	cfg := CFG{
		Name: "opaque_liveness", Entry: 1,
		Blocks: []Block{{
			ID: 1,
			Operations: []Operation{
				{Code: "memory.store", Effects: []Effect{EffectWriteMemory}},
				{Code: OpCall, Results: []Value{{ID: 1, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}}},
				{Code: "memory.store", Effects: []Effect{EffectWriteMemory}},
			},
			Terminator: Terminator{Kind: TerminatorReturn},
		}},
	}
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "heap", MemoryWrite),
			{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Kind: MemoryUnknownClobber}}},
			memoryMetadata(1, 2, "heap", MemoryWrite),
		},
	}
	analysis := analyzeMemoryLivenessForTest(t, cfg, metadata, RegionMemoryObservability{})
	if got, want := analysis.LiveAccesses, []MemoryAccessID{1, 2}; !reflect.DeepEqual(got, want) {
		t.Fatalf("opaque live accesses = %v, want %v", got, want)
	}
	if got, want := analysis.DeadAccessCandidates, []MemoryAccessID{3}; !reflect.DeepEqual(got, want) {
		t.Fatalf("opaque dead candidates = %v, want %v", got, want)
	}
}

func TestMemoryDefinitionLivenessVerifierRejectsStaleAndForgedEvidence(t *testing.T) {
	cfg := memoryLivenessLinearCFG("evidence", []Effect{EffectWriteMemory, EffectReadMemory})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			memoryMetadata(1, 0, "heap", MemoryWrite),
			memoryMetadata(1, 1, "heap", MemoryRead),
		},
	}
	observability := RegionMemoryObservability{}
	memorySSA := mustMemorySSA(t, cfg, metadata)
	analysis, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability)
	if err != nil {
		t.Fatal(err)
	}

	staleCFG := cfg
	staleCFG.Name = "other"
	if err := VerifyMemoryDefinitionLiveness(staleCFG, metadata, memorySSA, observability, analysis); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("stale CFG error = %v", err)
	}
	staleMetadata := metadata
	staleMetadata.Regions = []RegionID{"heap", "other"}
	if err := VerifyMemoryDefinitionLiveness(cfg, staleMetadata, memorySSA, observability, analysis); err == nil || !strings.Contains(err.Error(), "different metadata") {
		t.Fatalf("stale metadata error = %v", err)
	}
	staleSSA := memorySSA
	staleSSA.Accesses = append([]MemoryAccess(nil), memorySSA.Accesses...)
	staleSSA.Accesses[0].Input = 99
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, staleSSA, observability, analysis); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("stale memory SSA error = %v", err)
	}
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, RegionMemoryObservability{LiveOut: []RegionID{"heap"}}, analysis); err == nil || !strings.Contains(err.Error(), "different observability") {
		t.Fatalf("stale observability error = %v", err)
	}

	mutated := analysis
	mutated.LiveVersions = append([]MemoryVersionID(nil), analysis.LiveVersions...)
	mutated.LiveVersions[0] = 99
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability, mutated); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("mutated evidence error = %v", err)
	}
	forged := analysis
	forged.LiveVersions = append(forged.LiveVersions, 99)
	forged.integrity = fingerprintMemoryDefinitionLiveness(forged)
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability, forged); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("forged evidence error = %v", err)
	}
}

func analyzeMemoryLivenessForTest(t *testing.T, cfg CFG, metadata RegionMemoryMetadata, observability RegionMemoryObservability) MemoryDefinitionLiveness {
	t.Helper()
	memorySSA := mustMemorySSA(t, cfg, metadata)
	analysis, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability, analysis); err != nil {
		t.Fatal(err)
	}
	return analysis
}

func mustMemorySSA(t *testing.T, cfg CFG, metadata RegionMemoryMetadata) RegionMemorySSA {
	t.Helper()
	memorySSA, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	return memorySSA
}

func memoryMetadata(block BlockID, index int, region RegionID, kind MemoryAccessKind) MemoryOperationMetadata {
	return MemoryOperationMetadata{
		Site:     OperationSite{Block: block, Index: index},
		Accesses: []MemoryAccessSpec{{Region: region, Kind: kind}},
	}
}

func memoryLivenessLinearCFG(name string, effects []Effect) CFG {
	operations := make([]Operation, len(effects))
	for index, effect := range effects {
		operations[index] = Operation{Code: "memory.operation", Effects: []Effect{effect}}
	}
	return CFG{
		Name: name, Entry: 1,
		Blocks: []Block{{ID: 1, Operations: operations, Terminator: Terminator{Kind: TerminatorReturn}}},
	}
}

func containsMemoryVersion(values []MemoryVersionID, target MemoryVersionID) bool {
	for _, value := range values {
		if value == target {
			return true
		}
	}
	return false
}
