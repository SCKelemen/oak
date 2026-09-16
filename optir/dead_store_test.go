package optir

import (
	"reflect"
	"strings"
	"testing"
)

func TestDeadStoreEliminationRemovesExactOverwrittenStore(t *testing.T) {
	cfg := deadStoreCFG("overwrite", []Operation{
		deadStoreOperation(Fact{Name: "old-store", Values: []ValueID{1}}),
		deadStoreOperation(Fact{Name: "kept-store", Values: []ValueID{1}}),
		{Code: "memory.load", Effects: []Effect{EffectReadMemory}},
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			deadStoreMetadata(0, "heap", MemoryWrite, true, false),
			deadStoreMetadata(1, "heap", MemoryWrite, true, false),
			deadStoreMetadata(2, "heap", MemoryRead, false, false),
		},
	}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, RegionMemoryObservability{})
	result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, RegionMemoryObservability{}, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, RegionMemoryObservability{}, liveness, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	wantRemoved := []DeadStoreCandidate{{Access: 1, Version: 2, Region: "heap", Site: OperationSite{Block: 1, Index: 0}}}
	if !reflect.DeepEqual(report.Removed, wantRemoved) || len(report.Refused) != 0 || report.DroppedFacts != 1 {
		t.Fatalf("report = %+v, want removed %+v and one dropped fact", report, wantRemoved)
	}
	if got := result.Blocks[0].Operations; len(got) != 2 || got[0].Code != OpStoreRegion || got[0].Facts[0].Name != "kept-store" || got[1].Code != "memory.load" {
		t.Fatalf("result operations = %+v", got)
	}
	wantSites := []OperationSite{{Block: 1, Index: 0}, {Block: 1, Index: 1}}
	gotSites := []OperationSite{resultMetadata.Operations[0].Site, resultMetadata.Operations[1].Site}
	if !reflect.DeepEqual(gotSites, wantSites) {
		t.Fatalf("rewritten metadata sites = %v, want %v", gotSites, wantSites)
	}
	if len(cfg.Blocks[0].Operations) != 3 || cfg.Blocks[0].Operations[0].Facts[0].Name != "old-store" {
		t.Fatalf("input CFG was mutated: %+v", cfg.Blocks[0].Operations)
	}
}

func TestDeadStoreEliminationPreservesNoModRefCallMetadata(t *testing.T) {
	cfg := deadStoreCFG("no_modref_call", []Operation{
		deadStoreOperation(),
		{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "pure"}}},
		deadStoreOperation(),
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			deadStoreMetadata(0, "heap", MemoryWrite, true, false),
			{Site: OperationSite{Block: 1, Index: 1}, CallEffect: MemoryCallNoModRef},
			deadStoreMetadata(2, "heap", MemoryWrite, true, false),
		},
	}
	observability := RegionMemoryObservability{LiveOut: []RegionID{"heap"}}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, observability)
	result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, observability, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if len(report.Removed) != 1 || len(result.Blocks[0].Operations) != 2 {
		t.Fatalf("DSE result=%+v report=%+v", result, report)
	}
	if got := resultMetadata.Operations; len(got) != 2 || got[0].Site != (OperationSite{Block: 1, Index: 0}) ||
		got[0].CallEffect != MemoryCallNoModRef || len(got[0].Accesses) != 0 || got[1].Site != (OperationSite{Block: 1, Index: 1}) {
		t.Fatalf("rewritten no-ModRef metadata = %+v", got)
	}
}

func TestDeadStoreEliminationUsesAndPreservesRefCallReads(t *testing.T) {
	cfg := deadStoreCFG("ref_call", []Operation{
		deadStoreOperation(),
		deadStoreOperation(),
		{Code: OpCall, Results: []Value{{ID: 2, Type: "u32"}}, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "read-state"}}},
		deadStoreOperation(),
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"other", "state"},
		Operations: []MemoryOperationMetadata{
			deadStoreMetadata(0, "state", MemoryWrite, true, false),
			deadStoreMetadata(1, "other", MemoryWrite, true, false),
			{Site: OperationSite{Block: 1, Index: 2}, CallEffect: MemoryCallRef, Accesses: []MemoryAccessSpec{{Region: "state", Kind: MemoryRead}}},
			deadStoreMetadata(3, "other", MemoryWrite, true, false),
		},
	}
	observability := RegionMemoryObservability{LiveOut: []RegionID{"other"}}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, observability)
	result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, observability, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, result, resultMetadata, report); err != nil {
		t.Fatal(err)
	}
	if len(report.Removed) != 1 || report.Removed[0].Region != "other" || report.Removed[0].Site != (OperationSite{Block: 1, Index: 1}) {
		t.Fatalf("Ref DSE report = %+v", report)
	}
	if got := resultMetadata.Operations; len(got) != 3 || got[0].Accesses[0].Region != "state" ||
		got[1].CallEffect != MemoryCallRef || !reflect.DeepEqual(got[1].Accesses, []MemoryAccessSpec{{Region: "state", Kind: MemoryRead}}) ||
		got[2].Accesses[0].Region != "other" {
		t.Fatalf("Ref DSE metadata = %+v", got)
	}
}

func TestDeadStoreEliminationPreservesReadAndLiveOutDefinitions(t *testing.T) {
	tests := []struct {
		name          string
		operations    []Operation
		metadata      []MemoryOperationMetadata
		observability RegionMemoryObservability
	}{
		{
			name:       "read",
			operations: []Operation{deadStoreOperation(), {Code: "memory.load", Effects: []Effect{EffectReadMemory}}},
			metadata: []MemoryOperationMetadata{
				deadStoreMetadata(0, "heap", MemoryWrite, true, false),
				deadStoreMetadata(1, "heap", MemoryRead, false, false),
			},
		},
		{
			name:          "live-out",
			operations:    []Operation{deadStoreOperation()},
			metadata:      []MemoryOperationMetadata{deadStoreMetadata(0, "heap", MemoryWrite, true, false)},
			observability: RegionMemoryObservability{LiveOut: []RegionID{"heap"}},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := deadStoreCFG(test.name, test.operations)
			metadata := RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: test.metadata}
			memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, test.observability)
			result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, test.observability, liveness)
			if err != nil {
				t.Fatal(err)
			}
			if len(report.Removed) != 0 || !sameDeadStoreCFG(cfg, result) || !sameDeadStoreMetadata(t, cfg, metadata, result, resultMetadata) {
				t.Fatalf("observable definition changed: result=%+v metadata=%+v report=%+v", result, resultMetadata, report)
			}
		})
	}
}

func TestDeadStoreEliminationPartialOverwriteDoesNotKillPriorRegionState(t *testing.T) {
	cfg := deadStoreCFG("partial_overwrite", []Operation{
		deadStoreOperation(),
		{Code: "memory.partial-store", Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}},
		{Code: "memory.load", Effects: []Effect{EffectReadMemory}},
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			deadStoreMetadata(0, "heap", MemoryWrite, true, false),
			deadStoreMetadata(1, "heap", MemoryWrite, false, false),
			deadStoreMetadata(2, "heap", MemoryRead, false, false),
		},
	}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, RegionMemoryObservability{})
	if len(liveness.DeadAccessCandidates) != 0 {
		t.Fatalf("partial overwrite incorrectly killed prior region state: %+v", liveness)
	}
	result, _, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, RegionMemoryObservability{}, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if !sameDeadStoreCFG(cfg, result) || len(report.Removed) != 0 {
		t.Fatalf("partial overwrite changed CFG: result=%+v report=%+v", result, report)
	}
}

func TestDeadStoreEliminationRefusesOutsideClosedStoreContract(t *testing.T) {
	tests := []struct {
		name        string
		operation   Operation
		whole       bool
		volatile    bool
		want        DeadStoreRefusalReason
		noCandidate bool
	}{
		{name: "partial", operation: deadStoreOperation(), want: DeadStoreNotWholeRegion},
		{name: "volatile", operation: deadStoreOperation(), whole: true, volatile: true, noCandidate: true},
		{name: "extension", operation: Operation{Code: "memory.store", Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}}, whole: true, want: DeadStoreUnknownOperation},
		{name: "attribute", operation: Operation{Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}, Attributes: []Attribute{{Name: "mode", Value: "device"}}}, whole: true, want: DeadStoreHasAttributes},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cfg := deadStoreCFG(test.name, []Operation{test.operation})
			metadata := RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{
				deadStoreMetadata(0, "heap", MemoryWrite, test.whole, test.volatile),
			}}
			memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, RegionMemoryObservability{})
			result, _, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, RegionMemoryObservability{}, liveness)
			if err != nil {
				t.Fatal(err)
			}
			if !sameDeadStoreCFG(cfg, result) || len(report.Removed) != 0 {
				t.Fatalf("refused store changed: result=%+v report=%+v", result, report)
			}
			if test.noCandidate {
				if len(report.Refused) != 0 {
					t.Fatalf("volatile access should be a liveness root, report=%+v", report)
				}
				return
			}
			if len(report.Refused) != 1 || report.Refused[0].Reason != test.want {
				t.Fatalf("refusal = %+v, want %s", report.Refused, test.want)
			}
		})
	}
}

func TestDeadStoreEliminationRefusesTrappingMalformedClosedStore(t *testing.T) {
	cfg := deadStoreCFG("trap", []Operation{{
		Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory, EffectTrap},
	}})
	metadata := RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{
		deadStoreMetadata(0, "heap", MemoryWrite, true, false),
	}}
	if _, err := AnalyzeRegionMemorySSA(cfg, metadata); err == nil || !strings.Contains(err.Error(), "want exactly one memory-write effect") {
		t.Fatalf("trapping closed-store error = %v", err)
	}
}

func TestDeadStoreEliminationOpaqueCallKeepsReachingStore(t *testing.T) {
	cfg := deadStoreCFG("opaque", []Operation{
		deadStoreOperation(),
		{Code: OpCall, Effects: []Effect{EffectCall}, Attributes: []Attribute{{Name: AttributeCallee, Value: "opaque"}}, Results: []Value{{ID: 2, Type: "u32"}}},
	})
	metadata := RegionMemoryMetadata{
		Regions: []RegionID{"heap"},
		Operations: []MemoryOperationMetadata{
			deadStoreMetadata(0, "heap", MemoryWrite, true, false),
			{Site: OperationSite{Block: 1, Index: 1}, Accesses: []MemoryAccessSpec{{Kind: MemoryUnknownClobber}}},
		},
	}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, RegionMemoryObservability{})
	result, _, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, RegionMemoryObservability{}, liveness)
	if err != nil {
		t.Fatal(err)
	}
	if !sameDeadStoreCFG(cfg, result) || len(report.Removed) != 0 {
		t.Fatalf("opaque call did not preserve reaching store: result=%+v report=%+v", result, report)
	}
}

func TestDeadStoreEliminationKeepsPhiReachableDefinitions(t *testing.T) {
	tests := []struct {
		name     string
		cfg      CFG
		metadata RegionMemoryMetadata
	}{
		{
			name: "diamond",
			cfg:  memoryDiamondCFG(),
			metadata: RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{
				deadStoreMetadataAt(2, 0, "heap", MemoryWrite, true, false),
				deadStoreMetadataAt(4, 0, "heap", MemoryRead, false, false),
			}},
		},
		{
			name: "loop",
			cfg:  memoryLoopCFG(),
			metadata: RegionMemoryMetadata{Regions: []RegionID{"state"}, Operations: []MemoryOperationMetadata{
				deadStoreMetadataAt(3, 0, "state", MemoryReadWrite, true, false),
				deadStoreMetadataAt(4, 0, "state", MemoryRead, false, false),
			}},
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			memorySSA, liveness := deadStoreEvidence(t, test.cfg, test.metadata, RegionMemoryObservability{})
			result, _, report, err := EliminateDeadRegionStores(test.cfg, test.metadata, memorySSA, RegionMemoryObservability{}, liveness)
			if err != nil {
				t.Fatal(err)
			}
			if !sameDeadStoreCFG(test.cfg, result) || len(report.Removed) != 0 {
				t.Fatalf("phi-reachable definition changed: result=%+v report=%+v", result, report)
			}
		})
	}
}

func TestDeadStoreEliminationRejectsMalformedMetadata(t *testing.T) {
	cfg := deadStoreCFG("malformed", []Operation{{Code: "memory.load", Effects: []Effect{EffectReadMemory}}})
	metadata := RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{
		deadStoreMetadata(0, "heap", MemoryRead, true, false),
	}}
	if _, err := AnalyzeRegionMemorySSA(cfg, metadata); err == nil || !strings.Contains(err.Error(), "marks a read as a whole-region replacement") {
		t.Fatalf("whole-region read error = %v", err)
	}
}

func TestDeadStoreEliminationVerifierRejectsStaleAndForgedEvidence(t *testing.T) {
	cfg := deadStoreCFG("evidence", []Operation{deadStoreOperation()})
	metadata := RegionMemoryMetadata{Regions: []RegionID{"heap"}, Operations: []MemoryOperationMetadata{
		deadStoreMetadata(0, "heap", MemoryWrite, true, false),
	}}
	observability := RegionMemoryObservability{}
	memorySSA, liveness := deadStoreEvidence(t, cfg, metadata, observability)
	result, resultMetadata, report, err := EliminateDeadRegionStores(cfg, metadata, memorySSA, observability, liveness)
	if err != nil {
		t.Fatal(err)
	}

	staleCFG := cfg
	staleCFG.Name = "stale"
	if err := VerifyDeadStoreElimination(staleCFG, metadata, memorySSA, observability, liveness, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "different CFG") {
		t.Fatalf("stale CFG error = %v", err)
	}
	staleMetadata := metadata
	staleMetadata.Operations = append([]MemoryOperationMetadata(nil), metadata.Operations...)
	staleMetadata.Operations[0].Accesses = append([]MemoryAccessSpec(nil), metadata.Operations[0].Accesses...)
	staleMetadata.Operations[0].Accesses[0].WholeRegion = false
	if err := VerifyDeadStoreElimination(cfg, staleMetadata, memorySSA, observability, liveness, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "different metadata") {
		t.Fatalf("stale metadata error = %v", err)
	}
	staleSSA := memorySSA
	staleSSA.Accesses = append([]MemoryAccess(nil), memorySSA.Accesses...)
	staleSSA.Accesses[0].Input = 99
	if err := VerifyDeadStoreElimination(cfg, metadata, staleSSA, observability, liveness, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("stale SSA error = %v", err)
	}
	staleLiveness := liveness
	staleLiveness.DeadVersionCandidates = nil
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, staleLiveness, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("stale liveness error = %v", err)
	}
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, RegionMemoryObservability{LiveOut: []RegionID{"heap"}}, liveness, result, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "different observability") {
		t.Fatalf("stale observability error = %v", err)
	}

	mutatedReport := report
	mutatedReport.DroppedFacts++
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, result, resultMetadata, mutatedReport); err == nil || !strings.Contains(err.Error(), "was mutated") {
		t.Fatalf("mutated report error = %v", err)
	}
	staleResult := result
	staleResult.Name = "other-output"
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, staleResult, resultMetadata, report); err == nil || !strings.Contains(err.Error(), "different output CFG") {
		t.Fatalf("stale output error = %v", err)
	}
	staleOutputMetadata := resultMetadata
	staleOutputMetadata.Regions = []RegionID{"heap", "other"}
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, result, staleOutputMetadata, report); err == nil || !strings.Contains(err.Error(), "different output metadata") {
		t.Fatalf("stale output metadata error = %v", err)
	}
	forged := report
	forged.Removed = nil
	forged.integrity = fingerprintDeadStoreEliminationReport(forged)
	if err := VerifyDeadStoreElimination(cfg, metadata, memorySSA, observability, liveness, result, resultMetadata, forged); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("forged report error = %v", err)
	}
}

func deadStoreEvidence(t *testing.T, cfg CFG, metadata RegionMemoryMetadata, observability RegionMemoryObservability) (RegionMemorySSA, MemoryDefinitionLiveness) {
	t.Helper()
	memorySSA, err := AnalyzeRegionMemorySSA(cfg, metadata)
	if err != nil {
		t.Fatal(err)
	}
	liveness, err := AnalyzeMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability)
	if err != nil {
		t.Fatal(err)
	}
	return memorySSA, liveness
}

func deadStoreCFG(name string, operations []Operation) CFG {
	return CFG{
		Name: name, Entry: 1,
		Blocks: []Block{{
			ID: 1, Parameters: []Value{{ID: 1, Type: "u32"}},
			Operations: operations, Terminator: Terminator{Kind: TerminatorReturn},
		}},
	}
}

func deadStoreOperation(facts ...Fact) Operation {
	return Operation{
		Code: OpStoreRegion, Operands: []ValueID{1}, Effects: []Effect{EffectWriteMemory}, Facts: facts,
	}
}

func deadStoreMetadata(index int, region RegionID, kind MemoryAccessKind, whole, volatile bool) MemoryOperationMetadata {
	return deadStoreMetadataAt(1, index, region, kind, whole, volatile)
}

func deadStoreMetadataAt(block BlockID, index int, region RegionID, kind MemoryAccessKind, whole, volatile bool) MemoryOperationMetadata {
	return MemoryOperationMetadata{
		Site:     OperationSite{Block: block, Index: index},
		Accesses: []MemoryAccessSpec{{Region: region, Kind: kind, WholeRegion: whole, Volatile: volatile}},
	}
}

func sameDeadStoreCFG(left, right CFG) bool {
	return fingerprintCFG(left) == fingerprintCFG(right)
}

func sameDeadStoreMetadata(t *testing.T, leftCFG CFG, left RegionMemoryMetadata, rightCFG CFG, right RegionMemoryMetadata) bool {
	t.Helper()
	leftNormalized, err := normalizeMemoryMetadata(leftCFG, left)
	if err != nil {
		t.Fatal(err)
	}
	rightNormalized, err := normalizeMemoryMetadata(rightCFG, right)
	if err != nil {
		t.Fatal(err)
	}
	return fingerprintNormalizedMemoryMetadata(leftNormalized) == fingerprintNormalizedMemoryMetadata(rightNormalized)
}
