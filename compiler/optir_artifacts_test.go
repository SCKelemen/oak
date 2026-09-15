package compiler

import (
	"context"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/opt"
)

func TestOptIRAnalysesExecuteAsOneExactVersionedArtifactDAG(t *testing.T) {
	module, err := New().WithSource("artifact_loop.oak", `
count: (n: u32): u32 {
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

	first, err := runOptIRAnalysisGraph(function.CFG)
	if err != nil {
		t.Fatal(err)
	}
	second, err := runOptIRAnalysisGraph(function.CFG)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.keys, second.keys) || !reflect.DeepEqual(first.constants, second.constants) || !reflect.DeepEqual(first.loops, second.loops) || !reflect.DeepEqual(first.simplified, second.simplified) || !reflect.DeepEqual(first.loopInvariant, second.loopInvariant) {
		t.Fatal("OptIR artifact analysis is not deterministic")
	}
	graph, keys, err := newOptIRAnalysisGraph(function.CFG)
	if err != nil {
		t.Fatal(err)
	}
	wantOrder, err := graph.TopologicalOrder()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.run.Executed, wantOrder) || len(first.run.CacheHits) != 0 {
		t.Fatalf("artifact execution = %v, cache hits = %v, want order %v", first.run.Executed, first.run.CacheHits, wantOrder)
	}
	for _, key := range []opt.ArtifactKey{keys.cfgV0, keys.sccp, keys.loopsV0, keys.cleanup, keys.cfgV1, keys.loopsV1, keys.licm} {
		if _, exists := first.run.Artifact(key); !exists {
			t.Fatalf("artifact graph did not produce %s", key)
		}
	}
}

func TestOptIRArtifactCacheUsesExactKeysAndCFGChangesInvalidateEveryDependent(t *testing.T) {
	module, err := New().WithSource("artifact_constant.oak", `
answer: (): u32 = u32(40) + u32(2)
main: (): i32 = 0
`).OptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	function, exists := optIRFunction(module, "answer")
	if !exists {
		t.Fatalf("answer was not projected: %+v", module.Refusals)
	}
	graph, keys, err := newOptIRAnalysisGraph(function.CFG)
	if err != nil {
		t.Fatal(err)
	}
	targets := []opt.ArtifactKey{keys.sccp, keys.loopsV0, keys.cleanup, keys.licm}
	cache := opt.NewMemoryArtifactCache()
	first, err := graph.Run(context.Background(), cache, targets...)
	if err != nil {
		t.Fatal(err)
	}
	second, err := graph.Run(context.Background(), cache, targets...)
	if err != nil {
		t.Fatal(err)
	}
	if len(first.Executed) != 7 || len(second.Executed) != 0 || len(second.CacheHits) != len(targets) {
		t.Fatalf("cache evidence: first=%+v second=%+v", first, second)
	}

	changed := function.CFG
	changed.Name += ".changed"
	changedGraph, changedKeys, err := newOptIRAnalysisGraph(changed)
	if err != nil {
		t.Fatal(err)
	}
	before := []opt.ArtifactKey{keys.cfgV0, keys.sccp, keys.loopsV0, keys.cleanup, keys.cfgV1, keys.loopsV1, keys.licm}
	after := []opt.ArtifactKey{changedKeys.cfgV0, changedKeys.sccp, changedKeys.loopsV0, changedKeys.cleanup, changedKeys.cfgV1, changedKeys.loopsV1, changedKeys.licm}
	for index := range before {
		if before[index] == after[index] {
			t.Fatalf("CFG change did not invalidate artifact %s", before[index])
		}
	}
	changedRun, err := changedGraph.Run(context.Background(), cache, changedKeys.sccp, changedKeys.loopsV0, changedKeys.cleanup, changedKeys.licm)
	if err != nil {
		t.Fatal(err)
	}
	if len(changedRun.Executed) != 7 || len(changedRun.CacheHits) != 0 {
		t.Fatalf("changed CFG reused stale artifacts: %+v", changedRun)
	}
}
