package opt

import (
	"context"
	"errors"
	"reflect"
	"strconv"
	"strings"
	"testing"
)

func TestTypedArtifactBuildersDeriveOrderedKeysAndValues(t *testing.T) {
	leftKey := ArtifactKey{Kind: ArtifactIR, Name: "left", Version: "left-v1"}
	rightKey := ArtifactKey{Kind: ArtifactAnalysis, Name: "right", Version: "right-v1"}
	left, leftTask := RootArtifact(leftKey, 40)
	right, rightTask := RootArtifact(rightKey, "2")

	combined, combinedTask := DerivedArtifact2(ArtifactCandidate, "combine", "combine.v1", left, right,
		func(_ context.Context, number int, text string) (string, error) {
			return strconv.Itoa(number) + text, nil
		})
	length, lengthTask := DerivedArtifact1(ArtifactMetrics, "length", "length.v1", combined,
		func(_ context.Context, value string) (int, error) { return len(value), nil })
	verdict, verdictTask := DerivedArtifact3(ArtifactVerdict, "verdict", "verdict.v1", left, right, length,
		func(_ context.Context, number int, text string, size int) (bool, error) {
			return number == 40 && text == "2" && size == 3, nil
		})

	wantCombinedVersion := DeriveArtifactVersion("combine.v1", leftKey, rightKey)
	if combined.Key().Version != wantCombinedVersion || !reflect.DeepEqual(combinedTask.Dependencies, []ArtifactKey{leftKey, rightKey}) {
		t.Fatalf("combined identity/dependencies = %s %v", combined.Key(), combinedTask.Dependencies)
	}
	reversed := DeriveArtifactVersion("combine.v1", rightKey, leftKey)
	if combined.Key().Version == reversed {
		t.Fatal("typed builder erased dependency order")
	}

	graph, err := NewArtifactGraph(leftTask, rightTask, combinedTask, lengthTask, verdictTask)
	if err != nil {
		t.Fatal(err)
	}
	run, err := graph.Run(context.Background(), nil, verdict.Key())
	if err != nil {
		t.Fatal(err)
	}
	got, err := verdict.Value(run)
	if err != nil || !got {
		t.Fatalf("typed verdict = %v, %v", got, err)
	}
	if _, err := combined.Value(run); err != nil {
		t.Fatalf("typed intermediate missing: %v", err)
	}
}

func TestTypedArtifactBuilderRejectsWrongCachedPayload(t *testing.T) {
	rootKey := ArtifactKey{Kind: ArtifactIR, Name: "integer", Version: "v1"}
	root, rootTask := RootArtifact(rootKey, 41)
	derived, derivedTask := DerivedArtifact1(ArtifactAnalysis, "increment", "increment.v1", root,
		func(_ context.Context, value int) (int, error) { return value + 1, nil })
	graph, err := NewArtifactGraph(rootTask, derivedTask)
	if err != nil {
		t.Fatal(err)
	}
	cache := NewMemoryArtifactCache()
	cache.Put(rootKey, "not an integer")
	_, err = graph.Run(context.Background(), cache, derived.Key())
	if err == nil || !strings.Contains(err.Error(), "payload string, expected int") {
		t.Fatalf("wrong cached payload error = %v", err)
	}
}

func TestTypedArtifactReferenceRefusesMissingAndWrongRunValues(t *testing.T) {
	key := ArtifactKey{Kind: ArtifactAnalysis, Name: "answer", Version: "v1"}
	reference, _ := RootArtifact(key, 42)
	if _, err := reference.Value(ArtifactRun{}); err == nil || !strings.Contains(err.Error(), "was not produced") {
		t.Fatalf("missing artifact error = %v", err)
	}
	run := ArtifactRun{artifacts: map[ArtifactKey]Artifact{key: {Key: key, Value: errors.New("wrong")}}}
	if _, err := reference.Value(run); err == nil || !strings.Contains(err.Error(), "expected int") {
		t.Fatalf("wrong run payload error = %v", err)
	}
}

func TestTypedArtifactBuilderRefusesMissingCompute(t *testing.T) {
	key := ArtifactKey{Kind: ArtifactIR, Name: "root", Version: "v1"}
	root, rootTask := RootArtifact(key, 1)
	_, task := DerivedArtifact1[int, int](ArtifactAnalysis, "broken", "v1", root, nil)
	if _, err := NewArtifactGraph(rootTask, task); err == nil || !strings.Contains(err.Error(), "has no computation") {
		t.Fatalf("nil typed computation error = %v", err)
	}
}
