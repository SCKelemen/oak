package compiler

import (
	"context"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

func TestOptIRAnalysesExecuteAsOneExactVersionedArtifactDAG(t *testing.T) {
	module, err := New().WithSource("artifact_loop.oak", `
state: u32 = u32(0)

count: (n: u32): u32 {
	state = n
  i: u32 = u32(0)
  while i < n + u32(1) {
    i = i + u32(1)
  }
  i
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, exists := optIRFunction(module, "count")
	if !exists {
		t.Fatalf("count was not projected: %+v", module.Refusals)
	}

	first, err := runOptIRAnalysisGraphWithMemory(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	second, err := runOptIRAnalysisGraphWithMemory(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.keys, second.keys) || !reflect.DeepEqual(first.constants, second.constants) ||
		!reflect.DeepEqual(first.sccpSimplified, second.sccpSimplified) || !reflect.DeepEqual(first.sccpSimplification, second.sccpSimplification) ||
		!reflect.DeepEqual(first.loops, second.loops) || !reflect.DeepEqual(first.simplified, second.simplified) || !reflect.DeepEqual(first.loopInvariant, second.loopInvariant) {
		t.Fatal("OptIR artifact analysis is not deterministic")
	}
	graph, references, err := newOptIRAnalysisGraph(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	keys := references.keys()
	if keys.sccpRewrite.Name != "optir.sccp-rewrite" || keys.cleanup.Name != "optir.gvn-dce" || keys.preservation.Name != "optir.gvn-dce.preservation" {
		t.Fatalf("GVN/DCE artifact keys = %s, %s", keys.cleanup, keys.preservation)
	}
	wantOrder, err := graph.TopologicalOrder()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.run.Executed, wantOrder) || len(first.run.CacheHits) != 0 {
		t.Fatalf("artifact execution = %v, cache hits = %v, want order %v", first.run.Executed, first.run.CacheHits, wantOrder)
	}
	for _, key := range []opt.ArtifactKey{keys.cfgV0, keys.sccp, keys.sccpRewrite, keys.cfgV1, keys.loopStructureV1, keys.loopsV1, keys.cleanup, keys.cfgV2, keys.preservation, keys.loopsV2, keys.licm, keys.cfgV3, keys.memoryAuthority, keys.memoryProjection, keys.memorySSA, keys.memoryLiveness, keys.memoryEvidence, keys.dse} {
		if _, exists := first.run.Artifact(key); !exists {
			t.Fatalf("artifact graph did not produce %s", key)
		}
	}
	certificate, err := references.preservation.Value(first.run)
	if err != nil {
		t.Fatal(err)
	}
	if !certificate.Preserves(optir.LoopStructureAnalysisRequirements()) {
		t.Fatalf("GVN/DCE did not prove loop-structure preservation: %+v", certificate.Checks())
	}
}

func TestOptIRArtifactCacheUsesExactKeysAndCFGChangesInvalidateEveryDependent(t *testing.T) {
	module, err := New().WithSource("artifact_constant.oak", `
answer_state: u32 = u32(0)

answer: (): u32 {
  answer_state = u32(42)
  u32(40) + u32(2)
}
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, exists := optIRFunction(module, "answer")
	if !exists {
		t.Fatalf("answer was not projected: %+v", module.Refusals)
	}
	if function.SCCPRewrite.Changes() == 0 || len(function.SCCPSimplified.Blocks) == 0 {
		t.Fatalf("transformative SCCP was not exposed by OptIR: report=%+v cfg=%#v", function.SCCPRewrite, function.SCCPSimplified)
	}
	graph, references, err := newOptIRAnalysisGraph(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	keys := references.keys()
	targets := []opt.ArtifactKey{keys.sccp, keys.sccpRewrite, keys.loopsV1, keys.cleanup, keys.licm, keys.dse}
	cache := opt.NewMemoryArtifactCache()
	first, err := graph.Run(context.Background(), cache, targets...)
	if err != nil {
		t.Fatal(err)
	}
	second, err := graph.Run(context.Background(), cache, targets...)
	if err != nil {
		t.Fatal(err)
	}
	if len(first.Executed) != 18 || len(second.Executed) != 0 || len(second.CacheHits) != len(targets) {
		t.Fatalf("cache evidence: first=%+v second=%+v", first, second)
	}

	changed := function.CFG
	changed.Name += ".changed"
	changedGraph, changedReferences, err := newOptIRAnalysisGraph(changed, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	changedKeys := changedReferences.keys()
	before := []opt.ArtifactKey{keys.cfgV0, keys.sccp, keys.sccpRewrite, keys.cfgV1, keys.loopStructureV1, keys.loopsV1, keys.cleanup, keys.cfgV2, keys.preservation, keys.loopsV2, keys.licm, keys.cfgV3, keys.memoryProjection, keys.memorySSA, keys.memoryLiveness, keys.memoryEvidence, keys.dse}
	after := []opt.ArtifactKey{changedKeys.cfgV0, changedKeys.sccp, changedKeys.sccpRewrite, changedKeys.cfgV1, changedKeys.loopStructureV1, changedKeys.loopsV1, changedKeys.cleanup, changedKeys.cfgV2, changedKeys.preservation, changedKeys.loopsV2, changedKeys.licm, changedKeys.cfgV3, changedKeys.memoryProjection, changedKeys.memorySSA, changedKeys.memoryLiveness, changedKeys.memoryEvidence, changedKeys.dse}
	for index := range before {
		if before[index] == after[index] {
			t.Fatalf("CFG change did not invalidate artifact %s", before[index])
		}
	}
	changedRun, err := changedGraph.Run(context.Background(), cache, changedKeys.sccp, changedKeys.sccpRewrite, changedKeys.loopsV1, changedKeys.cleanup, changedKeys.licm, changedKeys.dse)
	if err != nil {
		t.Fatal(err)
	}
	if len(changedRun.Executed) != 17 || len(changedRun.CacheHits) != 1 {
		t.Fatalf("changed CFG reused stale artifacts: %+v", changedRun)
	}
}

func TestOptIRArtifactDAGOmitsMemoryAnalysesWithoutCheckedRegions(t *testing.T) {
	module, err := New().WithSource("artifact_call.oak", `
identity: (value: u32): u32 = value
caller: (value: u32): u32 = identity(value)
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, exists := optIRFunction(module, "caller")
	if !exists {
		t.Fatalf("caller was not projected: %+v", module.Refusals)
	}
	graph, references, err := newOptIRAnalysisGraph(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	order, err := graph.TopologicalOrder()
	if err != nil {
		t.Fatal(err)
	}
	if references.hasMemory || len(order) != 12 || references.dse.Key() != (opt.ArtifactKey{}) {
		t.Fatalf("call-only artifact graph has memory nodes: hasMemory=%t order=%v dse=%v", references.hasMemory, order, references.dse.Key())
	}
	analyses, err := runOptIRAnalysisGraphWithMemory(function.CFG, function.CheckedMemory)
	if err != nil {
		t.Fatal(err)
	}
	if analyses.hasMemory || len(analyses.deadStores.Blocks) != 0 {
		t.Fatalf("call-only analyses exposed memory candidates: %+v", analyses)
	}
}
