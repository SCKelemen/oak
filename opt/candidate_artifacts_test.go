package opt

import (
	"errors"
	"reflect"
	"strings"
	"testing"
)

func TestCandidateArtifactPipelineHasExplicitGates(t *testing.T) {
	driver := &fakeDriver{}
	candidate := Identity(config{})
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	findings, err := pipeline.admit(nodes)
	if err != nil || len(findings) != 0 {
		t.Fatalf("admission = %v, %v", findings, err)
	}
	candidate.Metrics, candidate.Cost, err = pipeline.measureAndCost(nodes)
	if err != nil {
		t.Fatal(err)
	}
	verdict, err := pipeline.validate(nodes)
	if err != nil {
		t.Fatal(err)
	}
	choice, err := pipeline.choose(
		[]Validated{{Candidate: candidate, Verdict: verdict}},
		[]*Candidate{candidate},
		map[*Candidate]candidateArtifactKeys{candidate: nodes},
		func(*Candidate) bool { return false },
	)
	if err != nil {
		t.Fatal(err)
	}
	if choice.candidate != nodes.candidate || choice.verdict.Outcome != Proven {
		t.Fatalf("choice = %+v", choice)
	}

	candidateTask := pipeline.graph.tasks[nodes.candidate]
	if nodes.input.Kind != ArtifactChecked || !reflect.DeepEqual(candidateTask.Dependencies, []ArtifactKey{nodes.input}) {
		t.Fatalf("materialization edge = %s -> %v", nodes.input, candidateTask.Dependencies)
	}
	verdictKey := pipeline.verdicts[nodes.candidate]
	verdictTask := pipeline.graph.tasks[verdictKey]
	wantVerdictDependencies := []ArtifactKey{nodes.candidate, nodes.admission, nodes.metrics, nodes.cost}
	if !reflect.DeepEqual(verdictTask.Dependencies, wantVerdictDependencies) {
		t.Fatalf("verdict dependencies = %v, want %v", verdictTask.Dependencies, wantVerdictDependencies)
	}
	var selectionTask ArtifactTask
	for key, task := range pipeline.graph.tasks {
		if key.Kind == ArtifactSelection {
			selectionTask = task
		}
	}
	wantSelectionDependencies := []ArtifactKey{nodes.candidate, nodes.admission, nodes.cost, verdictKey}
	if !reflect.DeepEqual(selectionTask.Dependencies, wantSelectionDependencies) {
		t.Fatalf("selection dependencies = %v, want %v", selectionTask.Dependencies, wantSelectionDependencies)
	}
	if len(driver.checked) != 1 || len(driver.measured) != 1 || len(driver.validated) != 1 {
		t.Fatalf("calls: checked %v, measured %v, validated %v", driver.checked, driver.measured, driver.validated)
	}
}

func TestCandidateArtifactRefusalClosesCostAndVerdictPaths(t *testing.T) {
	driver := &fakeDriver{findings: map[string][]string{"": {"f: refused"}}}
	candidate := Identity(config{})
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	findings, err := pipeline.admit(nodes)
	if err != nil || !reflect.DeepEqual(findings, []string{"f: refused"}) {
		t.Fatalf("admission = %v, %v", findings, err)
	}
	if _, _, err := pipeline.measureAndCost(nodes); err == nil || !strings.Contains(err.Error(), "metrics require clean admission") {
		t.Fatalf("cost after refusal error = %v", err)
	}
	if _, err := pipeline.validate(nodes); err == nil || !strings.Contains(err.Error(), "metrics require clean admission") {
		t.Fatalf("verdict after refusal error = %v", err)
	}
	if len(driver.measured) != 0 || len(driver.validated) != 0 {
		t.Fatalf("refusal leaked through gate: measured %v, validated %v", driver.measured, driver.validated)
	}
	if _, exists := pipeline.cache.Get(nodes.cost); exists {
		t.Fatal("refused candidate published a cost")
	}
	if _, exists := pipeline.cache.Get(pipeline.verdicts[nodes.candidate]); exists {
		t.Fatal("refused candidate published a verdict")
	}
}

func TestCandidateArtifactVerdictExecutesOnce(t *testing.T) {
	driver := &fakeDriver{}
	candidate := Identity(config{})
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	duplicate := Identity(config{})
	duplicateNodes, err := pipeline.materialize(duplicate)
	if err != nil {
		t.Fatal(err)
	}
	if duplicateNodes != nodes || duplicate.Key != candidate.Key || len(driver.lowered) != 1 {
		t.Fatalf("materialization cache: nodes %+v / %+v, keys %q / %q, lowered %v", nodes, duplicateNodes, candidate.Key, duplicate.Key, driver.lowered)
	}
	if _, err := pipeline.admit(nodes); err != nil {
		t.Fatal(err)
	}
	if _, _, err := pipeline.measureAndCost(nodes); err != nil {
		t.Fatal(err)
	}
	first, err := pipeline.validate(nodes)
	if err != nil {
		t.Fatal(err)
	}
	second, err := pipeline.validate(nodes)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(first, second) || len(driver.validated) != 1 {
		t.Fatalf("verdicts = %+v, %+v; validations = %v", first, second, driver.validated)
	}
}

func TestCandidateArtifactIdentityIncludesAndFreezesFacts(t *testing.T) {
	driver := &fakeDriver{}
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	fact := Fact{Proposition: Prop("aligned", "p", "16"), Provenance: Checked, Source: "typechecker", Scope: "f"}
	candidate := &Candidate{Config: config{}, Facts: []Fact{fact}}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	candidate.Facts[0].Proposition.Terms[0] = "mutated"

	duplicate := &Candidate{Config: config{}, Facts: []Fact{fact}}
	duplicateNodes, err := pipeline.materialize(duplicate)
	if err != nil {
		t.Fatal(err)
	}
	if duplicateNodes != nodes || duplicate.Facts[0].Proposition.Terms[0] != "p" || len(driver.lowered) != 1 {
		t.Fatalf("frozen duplicate: nodes %+v / %+v, facts %+v, lowered %v", nodes, duplicateNodes, duplicate.Facts, driver.lowered)
	}

	different := &Candidate{Config: config{}, Facts: []Fact{{Proposition: Prop("aligned", "q", "16"), Provenance: Checked, Source: "typechecker", Scope: "f"}}}
	differentNodes, err := pipeline.materialize(different)
	if err != nil {
		t.Fatal(err)
	}
	if differentNodes == nodes || len(driver.lowered) != 2 {
		t.Fatalf("distinct facts reused materialization: nodes %+v / %+v, lowered %v", nodes, differentNodes, driver.lowered)
	}
}

func TestCandidateArtifactFailedMaterializationIsNotPublished(t *testing.T) {
	loweringError := errors.New("sentinel lowering failure")
	driver := &fakeDriver{lowerErrs: map[string]error{"a": loweringError}}
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	for attempt := 0; attempt < 2; attempt++ {
		candidate := &Candidate{Applied: []string{"a"}, Config: config{switches: []string{"a"}}}
		if _, err := pipeline.materialize(candidate); err != loweringError {
			t.Fatalf("attempt %d error = %v", attempt, err)
		}
	}
	if !reflect.DeepEqual(driver.lowered, []string{"a", "a"}) {
		t.Fatalf("failed materialization was cached: lowered %v", driver.lowered)
	}
	for key := range pipeline.graph.tasks {
		if key.Kind != ArtifactCandidate {
			continue
		}
		if _, published := pipeline.cache.Get(key); published {
			t.Fatalf("failed materialization published %s", key)
		}
	}
}

func TestCandidateArtifactSelectionRequiresVerdict(t *testing.T) {
	driver := &fakeDriver{}
	candidate := Identity(config{})
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := pipeline.admit(nodes); err != nil {
		t.Fatal(err)
	}
	if _, _, err := pipeline.measureAndCost(nodes); err != nil {
		t.Fatal(err)
	}
	_, err = pipeline.choose(
		[]Validated{{Candidate: candidate, Verdict: Verdict{Outcome: Proven}}},
		[]*Candidate{candidate},
		map[*Candidate]candidateArtifactKeys{candidate: nodes},
		func(*Candidate) bool { return false },
	)
	if err == nil || !strings.Contains(err.Error(), "lacks verdict") {
		t.Fatalf("selection without verdict error = %v", err)
	}
}

func TestCandidateArtifactWeakGatedChoiceRequiresUngatedFallback(t *testing.T) {
	driver := &fakeDriver{verdicts: map[string]Outcome{"a": Trusted}}
	candidate := &Candidate{Applied: []string{"a"}, Config: config{switches: []string{"a"}}}
	pipeline, err := newCandidateArtifactPipeline("f", driver, AArch64Costs)
	if err != nil {
		t.Fatal(err)
	}
	nodes, err := pipeline.materialize(candidate)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := pipeline.admit(nodes); err != nil {
		t.Fatal(err)
	}
	candidate.Metrics, candidate.Cost, err = pipeline.measureAndCost(nodes)
	if err != nil {
		t.Fatal(err)
	}
	verdict, err := pipeline.validate(nodes)
	if err != nil {
		t.Fatal(err)
	}
	_, err = pipeline.choose(
		[]Validated{{Candidate: candidate, Verdict: verdict}},
		[]*Candidate{candidate},
		map[*Candidate]candidateArtifactKeys{candidate: nodes},
		func(*Candidate) bool { return true },
	)
	if err == nil || !strings.Contains(err.Error(), "no admitted, costed, and validated ungated fallback") {
		t.Fatalf("gated selection error = %v", err)
	}
}
