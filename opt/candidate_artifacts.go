package opt

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"strconv"
)

// candidateArtifactKeys are the typed gates for one exact materialized body.
// A verdict is added only when the bounded search elects to validate the body.
type candidateArtifactKeys struct {
	candidate ArtifactKey
	admission ArtifactKey
	metrics   ArtifactKey
	cost      ArtifactKey
}

type candidateArtifactValue struct {
	candidate *Candidate
}

type candidateAdmissionValue struct {
	candidate ArtifactKey
	findings  []string
}

type candidateMetricsValue struct {
	candidate ArtifactKey
	metrics   Metrics
}

type candidateCostValue struct {
	candidate ArtifactKey
	cost      float64
}

type candidateVerdictValue struct {
	candidate ArtifactKey
	verdict   Verdict
}

type candidateSelectionValue struct {
	candidate ArtifactKey
	verdict   Verdict
}

type candidateSelectionEntry struct {
	nodes   candidateArtifactKeys
	verdict ArtifactKey
	rank    int
	gated   bool
}

// candidateArtifactPipeline owns the ephemeral artifact graph for one region
// search. Its cache never escapes the search, because Config and Body are
// backend-owned values without a canonical freeze boundary yet.
type candidateArtifactPipeline struct {
	function string
	driver   Driver
	costs    CostModel
	graph    *ArtifactGraph
	cache    *MemoryArtifactCache
	nodes    map[ArtifactKey]candidateArtifactKeys
	verdicts map[ArtifactKey]ArtifactKey
}

func newCandidateArtifactPipeline(function string, driver Driver, costs CostModel) (*candidateArtifactPipeline, error) {
	graph, err := NewArtifactGraph()
	if err != nil {
		return nil, err
	}
	return &candidateArtifactPipeline{
		function: function,
		driver:   driver,
		costs:    costs,
		graph:    graph,
		cache:    NewMemoryArtifactCache(),
		nodes:    map[ArtifactKey]candidateArtifactKeys{},
		verdicts: map[ArtifactKey]ArtifactKey{},
	}, nil
}

// add records the candidate, admission, metrics, and cost recipes for one
// already-materialized body. Materialization remains the dynamic proposal
// search's responsibility until backend configurations have canonical keys.
func (pipeline *candidateArtifactPipeline) add(candidate *Candidate) (candidateArtifactKeys, error) {
	key := ArtifactKey{
		Kind:    ArtifactCandidate,
		Name:    "search.candidate",
		Version: candidateArtifactVersion(pipeline.function, candidate),
	}
	if nodes, exists := pipeline.nodes[key]; exists {
		return nodes, nil
	}

	snapshot := freezeCandidate(candidate)
	admission := ArtifactKey{
		Kind:    ArtifactAdmission,
		Name:    "search.admission",
		Version: DeriveArtifactVersion("oak.search.admission.v1", key),
	}
	metrics := ArtifactKey{
		Kind:    ArtifactMetrics,
		Name:    "search.metrics",
		Version: DeriveArtifactVersion("oak.search.metrics.v1", key, admission),
	}
	cost := ArtifactKey{
		Kind:    ArtifactCost,
		Name:    "search.cost",
		Version: DeriveArtifactVersion("oak.search.cost.v1:"+pipeline.costs.Name(), metrics),
	}
	nodes := candidateArtifactKeys{candidate: key, admission: admission, metrics: metrics, cost: cost}

	tasks := []ArtifactTask{
		{
			Key: key,
			Compute: func(context.Context, []Artifact) (any, error) {
				return candidateArtifactValue{candidate: snapshot}, nil
			},
		},
		{
			Key:          admission,
			Dependencies: []ArtifactKey{key},
			Compute: func(ctx context.Context, dependencies []Artifact) (any, error) {
				value, err := candidateDependencyValue[candidateArtifactValue](dependencies, 0)
				if err != nil {
					return nil, err
				}
				if err := ctx.Err(); err != nil {
					return nil, err
				}
				findings := pipeline.driver.Check(value.candidate)
				return candidateAdmissionValue{candidate: key, findings: append([]string(nil), findings...)}, nil
			},
		},
		{
			Key:          metrics,
			Dependencies: []ArtifactKey{key, admission},
			Compute: func(ctx context.Context, dependencies []Artifact) (any, error) {
				value, err := candidateDependencyValue[candidateArtifactValue](dependencies, 0)
				if err != nil {
					return nil, err
				}
				gate, err := candidateDependencyValue[candidateAdmissionValue](dependencies, 1)
				if err != nil {
					return nil, err
				}
				if gate.candidate != key || len(gate.findings) != 0 {
					return nil, fmt.Errorf("opt: metrics require clean admission for %s", key)
				}
				if err := ctx.Err(); err != nil {
					return nil, err
				}
				measured := freezeMetrics(pipeline.driver.Measure(value.candidate))
				return candidateMetricsValue{candidate: key, metrics: measured}, nil
			},
		},
		{
			Key:          cost,
			Dependencies: []ArtifactKey{metrics},
			Compute: func(_ context.Context, dependencies []Artifact) (any, error) {
				measured, err := candidateDependencyValue[candidateMetricsValue](dependencies, 0)
				if err != nil {
					return nil, err
				}
				if measured.candidate != key {
					return nil, fmt.Errorf("opt: cost metrics belong to %s, want %s", measured.candidate, key)
				}
				return candidateCostValue{candidate: key, cost: pipeline.costs.Estimate(measured.metrics)}, nil
			},
		},
	}
	for _, task := range tasks {
		if err := pipeline.graph.Add(task); err != nil {
			return candidateArtifactKeys{}, err
		}
	}
	pipeline.nodes[key] = nodes
	return nodes, nil
}

func (pipeline *candidateArtifactPipeline) admit(nodes candidateArtifactKeys) ([]string, error) {
	run, err := pipeline.graph.Run(context.Background(), pipeline.cache, nodes.admission)
	if err != nil {
		return nil, err
	}
	value, err := candidateRunValue[candidateAdmissionValue](run, nodes.admission)
	if err != nil {
		return nil, err
	}
	if value.candidate != nodes.candidate {
		return nil, fmt.Errorf("opt: admission belongs to %s, want %s", value.candidate, nodes.candidate)
	}
	return append([]string(nil), value.findings...), nil
}

func (pipeline *candidateArtifactPipeline) measureAndCost(nodes candidateArtifactKeys) (Metrics, float64, error) {
	run, err := pipeline.graph.Run(context.Background(), pipeline.cache, nodes.cost)
	if err != nil {
		return Metrics{}, 0, err
	}
	measured, err := candidateRunValue[candidateMetricsValue](run, nodes.metrics)
	if err != nil {
		return Metrics{}, 0, err
	}
	costed, err := candidateRunValue[candidateCostValue](run, nodes.cost)
	if err != nil {
		return Metrics{}, 0, err
	}
	if measured.candidate != nodes.candidate || costed.candidate != nodes.candidate {
		return Metrics{}, 0, fmt.Errorf("opt: metrics or cost are not bound to %s", nodes.candidate)
	}
	return freezeMetrics(measured.metrics), costed.cost, nil
}

// validate adds and requests a verdict only when the bounded search reaches
// this candidate. The explicit admission edge prevents the semantic verifier
// from becoming an alternate path around the seam checker.
func (pipeline *candidateArtifactPipeline) validate(nodes candidateArtifactKeys) (Verdict, error) {
	key, exists := pipeline.verdicts[nodes.candidate]
	if !exists {
		key = ArtifactKey{
			Kind:    ArtifactVerdict,
			Name:    "search.verdict",
			Version: DeriveArtifactVersion("oak.search.verdict.v1", nodes.candidate, nodes.admission, nodes.metrics, nodes.cost),
		}
		task := ArtifactTask{
			Key:          key,
			Dependencies: []ArtifactKey{nodes.candidate, nodes.admission, nodes.metrics, nodes.cost},
			Compute: func(ctx context.Context, dependencies []Artifact) (any, error) {
				value, err := candidateDependencyValue[candidateArtifactValue](dependencies, 0)
				if err != nil {
					return nil, err
				}
				gate, err := candidateDependencyValue[candidateAdmissionValue](dependencies, 1)
				if err != nil {
					return nil, err
				}
				measured, err := candidateDependencyValue[candidateMetricsValue](dependencies, 2)
				if err != nil {
					return nil, err
				}
				costed, err := candidateDependencyValue[candidateCostValue](dependencies, 3)
				if err != nil {
					return nil, err
				}
				if gate.candidate != nodes.candidate || measured.candidate != nodes.candidate || costed.candidate != nodes.candidate || len(gate.findings) != 0 {
					return nil, fmt.Errorf("opt: verdict requires matching clean admission, metrics, and cost for %s", nodes.candidate)
				}
				if err := ctx.Err(); err != nil {
					return nil, err
				}
				candidate := freezeCandidate(value.candidate)
				candidate.Metrics = freezeMetrics(measured.metrics)
				candidate.Cost = costed.cost
				verdict := freezeVerdict(pipeline.driver.Validate(candidate))
				return candidateVerdictValue{candidate: nodes.candidate, verdict: verdict}, nil
			},
		}
		if err := pipeline.graph.Add(task); err != nil {
			return Verdict{}, err
		}
		pipeline.verdicts[nodes.candidate] = key
	}
	run, err := pipeline.graph.Run(context.Background(), pipeline.cache, key)
	if err != nil {
		return Verdict{}, err
	}
	value, err := candidateRunValue[candidateVerdictValue](run, key)
	if err != nil {
		return Verdict{}, err
	}
	if value.candidate != nodes.candidate {
		return Verdict{}, fmt.Errorf("opt: verdict belongs to %s, want %s", value.candidate, nodes.candidate)
	}
	return freezeVerdict(value.verdict), nil
}

// choose constructs the only node allowed to choose an implementation. Every
// candidate it can return contributes candidate, admission, cost, and verdict
// dependencies. The search must validate an ungated fallback before calling
// this method when a weak verdict cannot license the leading candidate.
func (pipeline *candidateArtifactPipeline) choose(validated []Validated, order []*Candidate, artifacts map[*Candidate]candidateArtifactKeys, gated func(*Candidate) bool) (candidateSelectionValue, error) {
	ranks := make(map[*Candidate]int, len(order))
	for rank, candidate := range order {
		ranks[candidate] = rank
	}
	entries := make([]candidateSelectionEntry, 0, len(validated))
	dependencies := make([]ArtifactKey, 0, len(validated)*4)
	seen := make(map[ArtifactKey]bool, len(validated))
	for _, item := range validated {
		nodes, exists := artifacts[item.Candidate]
		if !exists {
			return candidateSelectionValue{}, fmt.Errorf("opt: selection lacks candidate artifacts for %s", item.Candidate.Name())
		}
		if seen[nodes.candidate] {
			return candidateSelectionValue{}, fmt.Errorf("opt: selection repeats candidate %s", nodes.candidate)
		}
		seen[nodes.candidate] = true
		verdict, exists := pipeline.verdicts[nodes.candidate]
		if !exists {
			return candidateSelectionValue{}, fmt.Errorf("opt: selection lacks verdict for %s", nodes.candidate)
		}
		rank, exists := ranks[item.Candidate]
		if !exists {
			return candidateSelectionValue{}, fmt.Errorf("opt: selection candidate %s is outside the ordered frontier", nodes.candidate)
		}
		entries = append(entries, candidateSelectionEntry{nodes: nodes, verdict: verdict, rank: rank, gated: gated(item.Candidate)})
		dependencies = append(dependencies, nodes.candidate, nodes.admission, nodes.cost, verdict)
	}
	if len(entries) == 0 {
		return candidateSelectionValue{}, fmt.Errorf("opt: selection has no validated candidate")
	}

	key := ArtifactKey{
		Kind:    ArtifactSelection,
		Name:    "search.selection",
		Version: DeriveArtifactVersion(candidateSelectionRevision(entries), dependencies...),
	}
	task := ArtifactTask{
		Key:          key,
		Dependencies: dependencies,
		Compute: func(_ context.Context, dependencies []Artifact) (any, error) {
			values := make([]candidateSelectionValue, len(entries))
			for index, entry := range entries {
				base := index * 4
				candidate, err := candidateDependencyValue[candidateArtifactValue](dependencies, base)
				if err != nil {
					return nil, err
				}
				gate, err := candidateDependencyValue[candidateAdmissionValue](dependencies, base+1)
				if err != nil {
					return nil, err
				}
				costed, err := candidateDependencyValue[candidateCostValue](dependencies, base+2)
				if err != nil {
					return nil, err
				}
				verdict, err := candidateDependencyValue[candidateVerdictValue](dependencies, base+3)
				if err != nil {
					return nil, err
				}
				if candidate.candidate == nil || gate.candidate != entry.nodes.candidate || costed.candidate != entry.nodes.candidate || verdict.candidate != entry.nodes.candidate || len(gate.findings) != 0 {
					return nil, fmt.Errorf("opt: selection gate is incomplete for %s", entry.nodes.candidate)
				}
				values[index] = candidateSelectionValue{candidate: entry.nodes.candidate, verdict: freezeVerdict(verdict.verdict)}
			}

			best := 0
			for index := 1; index < len(values); index++ {
				if values[index].verdict.Outcome > values[best].verdict.Outcome {
					best = index
				}
			}
			if values[best].verdict.Outcome <= Trusted && entries[best].gated {
				replacement := -1
				for index, entry := range entries {
					if entry.gated || replacement >= 0 && entries[replacement].rank <= entry.rank {
						continue
					}
					replacement = index
				}
				if replacement < 0 {
					return nil, fmt.Errorf("opt: gated candidate %s has no admitted, costed, and validated ungated fallback", entries[best].nodes.candidate)
				}
				best = replacement
			}
			return values[best], nil
		},
	}
	if err := pipeline.graph.Add(task); err != nil {
		return candidateSelectionValue{}, err
	}
	run, err := pipeline.graph.Run(context.Background(), pipeline.cache, key)
	if err != nil {
		return candidateSelectionValue{}, err
	}
	return candidateRunValue[candidateSelectionValue](run, key)
}

func candidateArtifactVersion(function string, candidate *Candidate) string {
	digest := sha256.New()
	writeArtifactDigestPart(digest, "oak.search.candidate.v1")
	writeArtifactDigestPart(digest, function)
	writeArtifactDigestPart(digest, candidate.Key)
	writeArtifactDigestPart(digest, strconv.Itoa(candidate.Refined))
	for _, transform := range candidate.Applied {
		writeArtifactDigestPart(digest, transform)
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func candidateSelectionRevision(entries []candidateSelectionEntry) string {
	digest := sha256.New()
	writeArtifactDigestPart(digest, "oak.search.selection.v1")
	for _, entry := range entries {
		writeArtifactDigestPart(digest, entry.nodes.candidate.String())
		writeArtifactDigestPart(digest, strconv.Itoa(entry.rank))
		writeArtifactDigestPart(digest, strconv.FormatBool(entry.gated))
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func freezeCandidate(candidate *Candidate) *Candidate {
	if candidate == nil {
		return nil
	}
	clone := *candidate
	clone.Applied = append([]string(nil), candidate.Applied...)
	clone.Facts = append([]Fact(nil), candidate.Facts...)
	clone.Metrics = freezeMetrics(candidate.Metrics)
	return &clone
}

func freezeMetrics(metrics Metrics) Metrics {
	metrics.LoopBodies = append([]LoopMetrics(nil), metrics.LoopBodies...)
	return metrics
}

func freezeVerdict(verdict Verdict) Verdict {
	verdict.Findings = append([]string(nil), verdict.Findings...)
	return verdict
}

func candidateDependencyValue[T any](dependencies []Artifact, index int) (T, error) {
	var zero T
	if index < 0 || index >= len(dependencies) {
		return zero, fmt.Errorf("opt: candidate artifact dependency %d is missing", index)
	}
	value, ok := dependencies[index].Value.(T)
	if !ok {
		return zero, fmt.Errorf("opt: candidate artifact %s has payload %T, expected %T", dependencies[index].Key, dependencies[index].Value, zero)
	}
	return value, nil
}

func candidateRunValue[T any](run ArtifactRun, key ArtifactKey) (T, error) {
	var zero T
	artifact, exists := run.Artifact(key)
	if !exists {
		return zero, fmt.Errorf("opt: candidate artifact run did not produce %s", key)
	}
	value, ok := artifact.Value.(T)
	if !ok {
		return zero, fmt.Errorf("opt: candidate artifact %s has payload %T, expected %T", key, artifact.Value, zero)
	}
	return value, nil
}
