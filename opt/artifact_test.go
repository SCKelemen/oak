package opt

import (
	"context"
	"errors"
	"reflect"
	"strings"
	"sync"
	"testing"
)

func artifactTestKey(kind ArtifactKind, name, version string) ArtifactKey {
	return ArtifactKey{Kind: kind, Name: name, Version: version}
}

func artifactTestTask(key ArtifactKey, dependencies []ArtifactKey, compute ArtifactCompute) ArtifactTask {
	return ArtifactTask{Key: key, Dependencies: dependencies, Compute: compute}
}

func TestDeriveArtifactVersionNamesExactOrderedRecipe(t *testing.T) {
	left := artifactTestKey(ArtifactIR, "cfg", "left")
	right := artifactTestKey(ArtifactAnalysis, "loops", "right")
	base := DeriveArtifactVersion("licm-v1", left, right)
	if base != DeriveArtifactVersion("licm-v1", left, right) {
		t.Fatal("artifact version is not deterministic")
	}
	tests := []string{
		DeriveArtifactVersion("licm-v2", left, right),
		DeriveArtifactVersion("licm-v1", right, left),
		DeriveArtifactVersion("licm-v1", artifactTestKey(ArtifactIR, "cfg", "other"), right),
		DeriveArtifactVersion("licm-v1", artifactTestKey(ArtifactAnalysis, "cfg", "left"), right),
	}
	for _, changed := range tests {
		if changed == base {
			t.Fatalf("changed recipe retained version %s", base)
		}
	}
	if DeriveArtifactVersion("r", artifactTestKey(ArtifactIR, "ab", "c")) == DeriveArtifactVersion("r", artifactTestKey(ArtifactIR, "a", "bc")) {
		t.Fatal("length-ambiguous keys produced one version")
	}
}

func TestArtifactGraphExecutesDiamondOnceInDependencyOrder(t *testing.T) {
	root := artifactTestKey(ArtifactIR, "cfg", "v0")
	left := artifactTestKey(ArtifactAnalysis, "dominance", DeriveArtifactVersion("v1", root))
	right := artifactTestKey(ArtifactAnalysis, "loops", DeriveArtifactVersion("v1", root))
	final := artifactTestKey(ArtifactCandidate, "licm", DeriveArtifactVersion("v1", right, left))
	orphan := artifactTestKey(ArtifactMetrics, "orphan", "v0")
	counts := map[ArtifactKey]int{}
	graph, err := NewArtifactGraph(
		artifactTestTask(final, []ArtifactKey{right, left}, func(_ context.Context, dependencies []Artifact) (any, error) {
			counts[final]++
			if len(dependencies) != 2 || dependencies[0].Key != right || dependencies[1].Key != left {
				t.Fatalf("dependency order = %+v", dependencies)
			}
			return dependencies[0].Value.(string) + "+" + dependencies[1].Value.(string), nil
		}),
		artifactTestTask(orphan, nil, func(context.Context, []Artifact) (any, error) {
			counts[orphan]++
			return "unused", nil
		}),
		artifactTestTask(right, []ArtifactKey{root}, func(_ context.Context, dependencies []Artifact) (any, error) {
			counts[right]++
			return dependencies[0].Value.(string) + ":loops", nil
		}),
		artifactTestTask(root, nil, func(context.Context, []Artifact) (any, error) {
			counts[root]++
			return "cfg", nil
		}),
		artifactTestTask(left, []ArtifactKey{root}, func(_ context.Context, dependencies []Artifact) (any, error) {
			counts[left]++
			return dependencies[0].Value.(string) + ":dom", nil
		}),
	)
	if err != nil {
		t.Fatal(err)
	}
	run, err := graph.Run(context.Background(), nil, final)
	if err != nil {
		t.Fatal(err)
	}
	wantExecuted := []ArtifactKey{root, left, right, final}
	if !reflect.DeepEqual(run.Executed, wantExecuted) || len(run.CacheHits) != 0 {
		t.Fatalf("execution evidence = %+v", run)
	}
	for _, key := range wantExecuted {
		if counts[key] != 1 {
			t.Fatalf("artifact %s executed %d times", key, counts[key])
		}
	}
	if counts[orphan] != 0 {
		t.Fatalf("artifact outside target closure executed %d times", counts[orphan])
	}
	artifact, exists := run.Artifact(final)
	if !exists || artifact.Value != "cfg:loops+cfg:dom" || len(run.Targets) != 1 || run.Targets[0].Key != final {
		t.Fatalf("final artifact = %+v, targets=%+v", artifact, run.Targets)
	}
}

func TestArtifactGraphOrderIgnoresRegistrationAndTargetOrder(t *testing.T) {
	a := artifactTestKey(ArtifactSource, "a", "v1")
	b := artifactTestKey(ArtifactSource, "b", "v1")
	compute := func(context.Context, []Artifact) (any, error) { return true, nil }
	first, err := NewArtifactGraph(artifactTestTask(b, nil, compute), artifactTestTask(a, nil, compute))
	if err != nil {
		t.Fatal(err)
	}
	second, err := NewArtifactGraph(artifactTestTask(a, nil, compute), artifactTestTask(b, nil, compute))
	if err != nil {
		t.Fatal(err)
	}
	firstOrder, err := first.TopologicalOrder()
	if err != nil {
		t.Fatal(err)
	}
	secondOrder, err := second.TopologicalOrder()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(firstOrder, secondOrder) || !reflect.DeepEqual(firstOrder, []ArtifactKey{a, b}) {
		t.Fatalf("orders = %v / %v", firstOrder, secondOrder)
	}
	left, err := first.Run(context.Background(), nil, b, a)
	if err != nil {
		t.Fatal(err)
	}
	right, err := second.Run(context.Background(), nil, a, b)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(left.Executed, right.Executed) || !reflect.DeepEqual(left.Targets, right.Targets) {
		t.Fatalf("target order affected run: %+v / %+v", left, right)
	}
}

func TestArtifactGraphCacheHitCutsOffDependencySubgraph(t *testing.T) {
	root := artifactTestKey(ArtifactIR, "cfg", "v0")
	analysis := artifactTestKey(ArtifactAnalysis, "sccp", DeriveArtifactVersion("v1", root))
	candidate := artifactTestKey(ArtifactCandidate, "fold", DeriveArtifactVersion("v1", analysis))
	counts := map[ArtifactKey]int{}
	compute := func(key ArtifactKey) ArtifactCompute {
		return func(context.Context, []Artifact) (any, error) {
			counts[key]++
			return key.String(), nil
		}
	}
	graph, err := NewArtifactGraph(
		artifactTestTask(candidate, []ArtifactKey{analysis}, compute(candidate)),
		artifactTestTask(analysis, []ArtifactKey{root}, compute(analysis)),
		artifactTestTask(root, nil, compute(root)),
	)
	if err != nil {
		t.Fatal(err)
	}
	cache := NewMemoryArtifactCache()
	first, err := graph.Run(context.Background(), cache, analysis)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first.Executed, []ArtifactKey{root, analysis}) || cache.Len() != 2 {
		t.Fatalf("first run = %+v, cache=%d", first, cache.Len())
	}
	second, err := graph.Run(context.Background(), cache, analysis)
	if err != nil {
		t.Fatal(err)
	}
	if len(second.Executed) != 0 || !reflect.DeepEqual(second.CacheHits, []ArtifactKey{analysis}) {
		t.Fatalf("cached target did not cut off dependencies: %+v", second)
	}
	third, err := graph.Run(context.Background(), cache, candidate)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(third.Executed, []ArtifactKey{candidate}) || !reflect.DeepEqual(third.CacheHits, []ArtifactKey{analysis}) {
		t.Fatalf("cached dependency was not reused: %+v", third)
	}
	if counts[root] != 1 || counts[analysis] != 1 || counts[candidate] != 1 {
		t.Fatalf("execution counts = %+v", counts)
	}
}

func TestArtifactGraphRejectsMalformedGraphs(t *testing.T) {
	compute := func(context.Context, []Artifact) (any, error) { return nil, nil }
	a := artifactTestKey(ArtifactIR, "a", "v1")
	b := artifactTestKey(ArtifactIR, "b", "v1")

	if _, err := NewArtifactGraph(artifactTestTask(ArtifactKey{Kind: "other", Name: "x", Version: "v1"}, nil, compute)); err == nil || !strings.Contains(err.Error(), "invalid kind") {
		t.Fatalf("invalid kind error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(ArtifactKey{Kind: ArtifactIR, Version: "v1"}, nil, compute)); err == nil || !strings.Contains(err.Error(), "empty name") {
		t.Fatalf("empty name error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(ArtifactKey{Kind: ArtifactIR, Name: "x"}, nil, compute)); err == nil || !strings.Contains(err.Error(), "empty version") {
		t.Fatalf("empty version error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(a, nil, nil)); err == nil || !strings.Contains(err.Error(), "no computation") {
		t.Fatalf("nil computation error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(a, nil, compute), artifactTestTask(a, nil, compute)); err == nil || !strings.Contains(err.Error(), "duplicate") {
		t.Fatalf("duplicate task error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(a, []ArtifactKey{b, b}, compute), artifactTestTask(b, nil, compute)); err == nil || !strings.Contains(err.Error(), "repeats dependency") {
		t.Fatalf("duplicate edge error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(a, []ArtifactKey{b}, compute)); err == nil || !strings.Contains(err.Error(), "missing artifact") {
		t.Fatalf("missing dependency error = %v", err)
	}
	if _, err := NewArtifactGraph(artifactTestTask(a, []ArtifactKey{b}, compute), artifactTestTask(b, []ArtifactKey{a}, compute)); err == nil || !strings.Contains(err.Error(), "cycle") {
		t.Fatalf("cycle error = %v", err)
	}
}

func TestArtifactGraphFailureAndCancellationAreAttributed(t *testing.T) {
	root := artifactTestKey(ArtifactIR, "cfg", "v0")
	failing := artifactTestKey(ArtifactAnalysis, "fail", "v0")
	dependent := artifactTestKey(ArtifactCandidate, "dependent", "v0")
	sentinel := errors.New("analysis refused")
	dependentRuns := 0
	graph, err := NewArtifactGraph(
		artifactTestTask(dependent, []ArtifactKey{failing}, func(context.Context, []Artifact) (any, error) {
			dependentRuns++
			return nil, nil
		}),
		artifactTestTask(failing, []ArtifactKey{root}, func(context.Context, []Artifact) (any, error) {
			return nil, sentinel
		}),
		artifactTestTask(root, nil, func(context.Context, []Artifact) (any, error) { return "cfg", nil }),
	)
	if err != nil {
		t.Fatal(err)
	}
	run, err := graph.Run(context.Background(), nil, dependent)
	var failure *ArtifactTaskError
	if !errors.As(err, &failure) || failure.Key != failing || !errors.Is(err, sentinel) || dependentRuns != 0 || !reflect.DeepEqual(run.Executed, []ArtifactKey{root}) {
		t.Fatalf("failure run=%+v err=%v dependent=%d", run, err, dependentRuns)
	}

	cancelled, cancel := context.WithCancel(context.Background())
	cancel()
	run, err = graph.Run(cancelled, nil, root)
	if !errors.As(err, &failure) || failure.Key != root || !errors.Is(err, context.Canceled) || len(run.Executed) != 0 {
		t.Fatalf("cancelled run=%+v err=%v", run, err)
	}
	if _, err := graph.Run(nil, nil, root); err == nil || !strings.Contains(err.Error(), "nil context") {
		t.Fatalf("nil context error = %v", err)
	}

	duringKey := artifactTestKey(ArtifactAnalysis, "cancel-during-compute", "v0")
	duringContext, cancelDuring := context.WithCancel(context.Background())
	duringGraph, err := NewArtifactGraph(artifactTestTask(duringKey, nil, func(context.Context, []Artifact) (any, error) {
		cancelDuring()
		return "must not publish", nil
	}))
	if err != nil {
		t.Fatal(err)
	}
	cache := NewMemoryArtifactCache()
	run, err = duringGraph.Run(duringContext, cache, duringKey)
	if !errors.As(err, &failure) || failure.Key != duringKey || !errors.Is(err, context.Canceled) || len(run.Executed) != 0 || cache.Len() != 0 {
		t.Fatalf("mid-compute cancellation run=%+v err=%v cache=%d", run, err, cache.Len())
	}
}

func TestArtifactGraphCopiesDeclaredDependencies(t *testing.T) {
	root := artifactTestKey(ArtifactIR, "cfg", "v0")
	target := artifactTestKey(ArtifactAnalysis, "loops", "v0")
	dependencies := []ArtifactKey{root}
	graph := &ArtifactGraph{}
	if err := graph.Add(artifactTestTask(root, nil, func(context.Context, []Artifact) (any, error) { return "cfg", nil })); err != nil {
		t.Fatal(err)
	}
	if err := graph.Add(artifactTestTask(target, dependencies, func(_ context.Context, inputs []Artifact) (any, error) {
		return inputs[0].Key, nil
	})); err != nil {
		t.Fatal(err)
	}
	dependencies[0] = artifactTestKey(ArtifactIR, "mutated", "v0")
	run, err := graph.Run(context.Background(), nil, target)
	if err != nil {
		t.Fatal(err)
	}
	artifact, exists := run.Artifact(target)
	if !exists || artifact.Value != root {
		t.Fatalf("dependency slice was not copied: %+v", artifact)
	}
}

func TestMemoryArtifactCacheSupportsConcurrentCompilerWork(t *testing.T) {
	cache := NewMemoryArtifactCache()
	const workers = 24
	var wait sync.WaitGroup
	for worker := 0; worker < workers; worker++ {
		worker := worker
		wait.Add(1)
		go func() {
			defer wait.Done()
			key := artifactTestKey(ArtifactAnalysis, "worker", string(rune('a'+worker)))
			for round := 0; round < 100; round++ {
				cache.Put(key, round)
				if _, exists := cache.Get(key); !exists {
					t.Errorf("worker %d lost its cached value", worker)
					return
				}
			}
		}()
	}
	wait.Wait()
	if cache.Len() != workers {
		t.Fatalf("cache has %d entries, want %d", cache.Len(), workers)
	}
}
